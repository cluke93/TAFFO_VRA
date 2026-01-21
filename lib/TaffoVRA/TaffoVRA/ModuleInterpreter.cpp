#include "ValueRangeAnalysisPass.hpp"
#include "ModuleInterpreter.hpp"
#include "TaffoInfo/TaffoInfo.hpp"

#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Analysis/IVDescriptors.h>
#include <llvm/Analysis/ScalarEvolutionExpressions.h>

#include <cassert>
#include <deque>

#define DEBUG_TYPE "taffo-vra"

using namespace llvm;

namespace taffo {

static bool isLoopLatch(const llvm::Loop* L, llvm::BasicBlock* candidate) {
    llvm::SmallVector<llvm::BasicBlock*, 4> latches;
    L->getLoopLatches(latches);

    auto it = std::find(latches.begin(), latches.end(), candidate);
    return it != latches.end();
}

static bool isLoopExit(const llvm::Loop* L, llvm::BasicBlock* candidate) {
    llvm::SmallVector<llvm::BasicBlock*, 4> exits;
    L->getExitBlocks(exits);

    auto it = std::find(exits.begin(), exits.end(), candidate);
    return it != exits.end();
}

static void collectLoopsPostOrder(Loop *L, SmallVectorImpl<Loop*> &Out) {
  for (Loop *SubL : L->getSubLoops()) {
    collectLoopsPostOrder(SubL, Out);
  }
  Out.push_back(L);
}

static SmallVector<Loop*> getLoopsInnermostFirst(Function *F, LoopInfo &LI) {
  SmallVector<Loop*> Result;
  for (Loop *TopL : LI) {
    collectLoopsPostOrder(TopL, Result);
  }
  return Result;
}

static const Value* getBaseMemoryObject(const Value* Ptr) {
    if (!Ptr) return nullptr;
    Ptr = Ptr->stripPointerCasts();

    const Value* Base = getUnderlyingObject(Ptr, 6);
    if (!Base) Base = Ptr;

    return Base->stripPointerCasts();
}

std::shared_ptr<AnalysisStore> ModuleInterpreter::getStoreForValue(const llvm::Value* V) const {
    assert(V && "Trying to get AnalysisStore for null value.");

    if (llvm::isa<llvm::Constant>(V))
        return GlobalStore;

    if (llvm::isa<llvm::Argument>(V)) {

        for (auto [F, VFI] : FNs) {
            if (VFI.scope.FunctionStore->hasValue(V)) return VFI.scope.FunctionStore;

            if (const llvm::Instruction* I = llvm::dyn_cast<llvm::Instruction>(V)) {

                auto BBAIt = VFI.scope.BBAnalyzers.find(I->getParent());
                if (BBAIt != VFI.scope.BBAnalyzers.end() && BBAIt->second->hasValue(I)) return BBAIt->second;
            }
        }
    }
    return nullptr;
}

void ModuleInterpreter::interpret() {

    preSeed();
    if (FNs.size() == 0) return;

    LLVM_DEBUG(tda::log() << "\n\n------------------------------------------------------------------------------\n");
    LLVM_DEBUG(tda::log() << "preseed completed: found " << FNs.size() << " visitable functions with " << countLoops() <<" loops.\n");
    LLVM_DEBUG(tda::log() <<   "------------------------------------------------------------------------------\n\n");

    inspect();

    LLVM_DEBUG(tda::log() << "\n\n------------------------------------------------------------------------------\n");
    LLVM_DEBUG(tda::log() << "inspection completed: found " << countPotentialRecurrences() << " potential detectable recurrences.\n");
    LLVM_DEBUG(tda::log() <<   "------------------------------------------------------------------------------\n\n");

    // size_t iteration = 1;
    // size_t changes = 0;
    // do {

    //     assemble();

    //     //todo: check at least one loop without trip count
    //     if (true) {
    //         tripCount();
    //     }

    //     propagate();


    //     ++iteration;
    //     if (MaxPropagation && iteration > MaxPropagation) {
    //         LLVM_DEBUG(tda::log() << "Propagation interrupted: after " << MaxPropagation << " iteration(s) no fixed point reached\n");
    //         break;
    //     }
    // } while (changes != 0);

}

//==================================================================================================
//======================= PRESEEDING METHODS =======================================================
//==================================================================================================

void ModuleInterpreter::preSeed() {

    bool FoundVisitableFunction = false;
    for (Function& F : M) {
        if (!F.empty() && (TaffoInfo::getInstance().isStartingPoint(F)) && F.getName() == "main") {

            
            interpretFunction(&F);

            FoundVisitableFunction = true;
        }
    }

    if (!FoundVisitableFunction) {
        LLVM_DEBUG(tda::log() << " No visitable functions found.\n");
    }

}

void ModuleInterpreter::interpretFunction(llvm::Function* F, std::shared_ptr<AnalysisStore> FunctionStore) {


    if (FNs.count(F)) {
        LLVM_DEBUG(tda::log() << "FN["<<F->getName()<<"] already interpreted\n");
        return;
    }

    auto InsertRes = FNs.try_emplace(F, VRAFunctionInfo(F, MAM));
    VRAFunctionInfo& VFI = InsertRes.first->second;

    if (!FunctionStore)
        FunctionStore = GlobalStore->newFnStore(*this);
    VFI.scope = FunctionScope(FunctionStore);
    curFn.push_back(F);

    llvm::BasicBlock* EntryBlock = &F->getEntryBlock();
    llvm::SmallPtrSet<llvm::BasicBlock*, 4U> VisitedSuccs;
    std::deque<llvm::BasicBlock*> worklist;
    llvm::SmallVector<llvm::Loop*> curLoop;

    worklist.push_back(EntryBlock);
    VFI.scope.BBAnalyzers[EntryBlock] = GlobalStore->newInstructionAnalyzer(*this);

    while (!worklist.empty()) {
        llvm::BasicBlock* curBlock = worklist.front();
        worklist.pop_front();

        auto CAIt = VFI.scope.BBAnalyzers.find(curBlock);
        assert(CAIt != VFI.scope.BBAnalyzers.end());
        std::shared_ptr<CodeAnalyzer> CurAnalyzer = CAIt->second;

        for (llvm::Instruction& I : *curBlock) {
            if (CurAnalyzer->requiresInterpretation(&I)) {
                interpretCall(CurAnalyzer, &I);
            } else {
                //CurAnalyzer->analyzeInstruction(&I);
            }
        }

        if (curLoop.empty()) {
            LLVM_DEBUG(tda::log() << "BB["<<curBlock->getName()<<"] marked as visited\n");
            VFI.bbFlow.push_back(curBlock);
        } else {
            LLVM_DEBUG(tda::log() << "BB["<<curBlock->getName()<<"] marked as visited into the loop " << curLoop.back()->getName() << "\n");
            VFI.loops[curLoop.back()].bbFlow.push_back(curBlock);
        }

        llvm::Instruction* Term = curBlock->getTerminator();
        VisitedSuccs.clear();
        for (unsigned NS = 0; NS < Term->getNumSuccessors(); ++NS) {
            llvm::BasicBlock* nextBlock = Term->getSuccessor(NS);

            // Needed just for terminators where the same successor appears twice
            if (VisitedSuccs.count(nextBlock)) continue;
            else VisitedSuccs.insert(nextBlock);

            LLVM_DEBUG(tda::log() << "FN["<<F->getName()<<"] >> Follow path "<<curBlock->getName()<<" ==> "<<nextBlock->getName()<<": ");
            switch(followPath(VFI, curBlock, nextBlock, curLoop)) {
                case FollowingPathResponse::ENQUE_BLOCK: {
                    LLVM_DEBUG(tda::log() << "ENQUE_BLOCK.\n");
                    worklist.push_front(nextBlock);
                    break;
                }
                case FollowingPathResponse::LOOP_FORK: {
                    LLVM_DEBUG(tda::log() << "LOOP_FORK. New VRALoopInfo created, new context, header enqueued ==> ");

                    // add also loop header to trace when go into loop into propagate phase()
                    if (curLoop.empty()) {
                        LLVM_DEBUG(tda::log() << "added loop header to bbFlow\n");
                        VFI.bbFlow.push_back(nextBlock);
                    } else {
                        LLVM_DEBUG(tda::log() << "added loop header to bbFlow of the loop " << curLoop.back()->getName() << "\n");
                        VFI.loops[curLoop.back()].bbFlow.push_back(nextBlock);
                    }

                    //here nextBlock is the new loop header
                    Loop* dstLoop = VFI.LI->getLoopFor(nextBlock);
                    curLoop.push_back(dstLoop);
                    VFI.loops.try_emplace(dstLoop, VRALoopInfo(dstLoop));
                    worklist.push_front(nextBlock);

                    break;
                }
                case FollowingPathResponse::LOOP_JOIN: {
                    LLVM_DEBUG(tda::log() << "LOOP_JOIN. Old context restored, exits enqueued\n");
                    llvm::Loop* dstLoop = curLoop.back();
                    curLoop.pop_back();

                    SmallVector<BasicBlock*, 4> exits;
                    dstLoop->getExitBlocks(exits);
                    for (BasicBlock* EB : exits) {
                        worklist.push_back(EB);
                    }

                    break;
                }
                default: {
                    LLVM_DEBUG(tda::log() << "NO ACTION.\n");
                    break;
                }
            }

            updateSuccessorAnalyzer(CurAnalyzer, Term, NS);
        }
        GlobalStore->convexMerge(*CurAnalyzer);
    }
    curFn.pop_back();
}

FollowingPathResponse ModuleInterpreter::followPath(VRAFunctionInfo info, llvm::BasicBlock* src, llvm::BasicBlock* dst, llvm::SmallVector<llvm::Loop*> nesting) const {

    llvm::Loop* srcLoop = info.LI->getLoopFor(src);
    llvm::Loop* dstLoop = info.LI->getLoopFor(dst);

    if (srcLoop && isLoopExit(srcLoop, dst)) return FollowingPathResponse::NO_ENQUE;

    llvm::SmallVector<llvm::BasicBlock *> curFlow;
    if (!srcLoop) curFlow = info.bbFlow;                                                                               // flow preso dal corpo della funzione
    else if (nesting.back() == srcLoop) curFlow = info.loops.lookup(srcLoop).bbFlow;                         //flow da analizzare preso dal loop corrente
    
    for (BasicBlock* pred : predecessors(dst)) {

        // do not analyze header predecessors if latch
        llvm::Loop* predLoop = info.LI->getLoopFor(pred);
        if (predLoop && isLoopLatch(predLoop, pred) && dst == predLoop->getHeader()) continue;
        if (dstLoop && predLoop == dstLoop->getParentLoop() && dstLoop->getHeader() == dst) continue;               // blocco prima del loop più esterno per forza visitato

        // typically loop exits path
        if (predLoop && dstLoop && info.loops.count(predLoop) && dstLoop == predLoop->getParentLoop()) {
            VRALoopInfo loopInfo = info.loops.lookup(predLoop);
            if (!loopInfo.isEntirelyVisited()) {
                LLVM_DEBUG(tda::log() << "pred loop " << predLoop->getName() << " is not entirely visited yet ==> ");
                return FollowingPathResponse::NO_ENQUE;
            }
        }

        auto it = std::find(curFlow.begin(), curFlow.end(), pred);
        if (it == curFlow.end()) {
            LLVM_DEBUG(tda::log() << "pred block " << pred->getName() << " is not visited yet ==> ");
            return FollowingPathResponse::NO_ENQUE;
        }
    }
    
    // percorso da esterno a nuovo loop
    if (dstLoop && dstLoop->getHeader() == dst && srcLoop != dstLoop) {
        if (!info.loops.count(dstLoop)) {
        return FollowingPathResponse::LOOP_FORK;
        }
    }
    
    // latch del loop che punta al suo header:
    if (dstLoop && dstLoop->getHeader() == dst && srcLoop == dstLoop && isLoopLatch(srcLoop, src)) {
        // torna loop join se il loop risulta completamente visitato, altrimenti no_enque
        LLVM_DEBUG(tda::log() << "path latch -> header (same loop) ==> ");
        return info.loops.lookup(srcLoop).isEntirelyVisited() ? FollowingPathResponse::LOOP_JOIN : FollowingPathResponse::NO_ENQUE;
    }
    
    // path standard: se non visitato permetti, altrimenti evita
    auto it = std::find(curFlow.begin(), curFlow.end(), dst);
    return it == curFlow.end() ? FollowingPathResponse::ENQUE_BLOCK : FollowingPathResponse::NO_ENQUE;
}

void ModuleInterpreter::updateSuccessorAnalyzer(std::shared_ptr<CodeAnalyzer> CurrentAnalyzer, llvm::Instruction* TermInstr, unsigned SuccIdx) {
    llvm::DenseMap<llvm::BasicBlock*, std::shared_ptr<CodeAnalyzer>>& BBAnalyzers = FNs[curFn.back()].scope.BBAnalyzers;
    llvm::BasicBlock* SuccBB = TermInstr->getSuccessor(SuccIdx);

    std::shared_ptr<CodeAnalyzer> SuccAnalyzer;
    auto SAIt = BBAnalyzers.find(SuccBB);
    if (SAIt == BBAnalyzers.end()) {
        SuccAnalyzer = CurrentAnalyzer->clone();
        BBAnalyzers[SuccBB] = SuccAnalyzer;
    }
    else {
        SuccAnalyzer = SAIt->second;
        SuccAnalyzer->convexMerge(*CurrentAnalyzer);
    }

    CurrentAnalyzer->setPathLocalInfo(SuccAnalyzer, TermInstr, SuccIdx);
}

void ModuleInterpreter::interpretCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I) {
    llvm::CallBase* CB = llvm::cast<llvm::CallBase>(I);
    llvm::Function* F = CB->getCalledFunction();
    if (!F || F->empty())
        return;

    std::shared_ptr<AnalysisStore> FunctionStore = GlobalStore->newFnStore(*this);

    CurAnalyzer->prepareForCall(I, FunctionStore);
    interpretFunction(F, FunctionStore);
    CurAnalyzer->returnFromCall(I, FunctionStore);
}


//==================================================================================================
//======================= INSPECTION METHODS =======================================================
//==================================================================================================

void ModuleInterpreter::inspect() {

    for (auto &Entry : FNs) {
        llvm::Function *F = Entry.first;
        auto &VFI = Entry.second;
        
        for (llvm::Loop *L : getLoopsInnermostFirst(F, *VFI.LI)) {
            for (BasicBlock* loopBlock : L->blocks()) {
                for (Instruction& I : *loopBlock) {
                    if (!isa<PHINode>(I) && !isa<StoreInst>(I)) continue;

                    VRARecurrenceInfo VRI(static_cast<const llvm::Value*>(&I));
                    if (isa<PHINode>(I) && loopBlock == L->getHeader()) {
                        handlePHIChain(VFI, L, dyn_cast<PHINode>(&I), VRI);

                        if (isInductionVariable(F, L, dyn_cast<PHINode>(&I))) {
                            VFI.loops[L].InductionVariable = dyn_cast<PHINode>(&I);
                        }
                    } else if (isa<StoreInst>(I)) {
                        handleStoreChain(VFI, L, dyn_cast<StoreInst>(&I), VRI);
                    }

                    if (VRI.isValid()) VFI.RRs.try_emplace(static_cast<const llvm::Value*>(&I), VRI);
                }
            }
        }
    }
}

bool ModuleInterpreter::isInductionVariable(llvm::Function *F, llvm::Loop* L, const llvm::PHINode* PHI) {
    if (!L || !PHI) return false;

    // 1) Canonical IV (fast path).
    if (const PHINode *CIV = L->getCanonicalInductionVariable())
        if (CIV == PHI) return true;

    // Must be a PHI in the loop header.
    if (PHI->getParent() != L->getHeader()) return false;

        auto SE = FNs[F].SE;

    // 2) Use IVDescriptors when SCEV is available (handles many non-canonical cases).
    if (SE && SE->isSCEVable(PHI->getType())) {
        InductionDescriptor D;
        auto *PN = const_cast<llvm::PHINode*>(PHI);
        if (InductionDescriptor::isInductionPHI(PN, L, SE, D)) return true;

        // 3) SCEV fallback: PN is an add recurrence on L with invariant start/step.
        const SCEV *S = SE->getSCEV(const_cast<PHINode*>(PHI));
        if (const auto *AR = dyn_cast<SCEVAddRecExpr>(S)) {
            if (AR->getLoop() == L) {
                const SCEV *Start = AR->getStart();
                const SCEV *Step  = AR->getStepRecurrence(*SE);
                if (SE->isLoopInvariant(Start, L) && SE->isLoopInvariant(Step, L))
                return true;
            }
        }
    }

    //todo: expand here new way to detect IV
    return false;
}

void ModuleInterpreter::handlePHIChain(VRAFunctionInfo VFI, Loop* L, const PHINode* PHI, VRARecurrenceInfo& VRI) {

    VRI.kind = VRAInspectionKind::UNKNOWN;

    // retrieve PHI latch
    const Value *latchIncoming = nullptr;
    if (auto *latch = L->getLoopLatch()) {
        latchIncoming = PHI->getIncomingValueForBlock(latch);
    }
    if (!latchIncoming) {
        LLVM_DEBUG(tda::log() << " missing latch incoming block, abort\n");
        VRI.chain.clear();
        return;
    }

    SmallVector<const Value*, 32> worklist;
    DenseMap<const Value*, const Value*> preds;
    auto enqueue = [&](const Value *from, const Value *to) {
        if (preds.contains(to)) return;
        preds[to] = from;
        worklist.push_back(to);
    };

    preds[PHI] = nullptr;
    worklist.push_back(PHI);

    while (!worklist.empty()) {
        const Value *cur = worklist.pop_back_val();

        if (cur == latchIncoming) {
            SmallVector<const Value*, 32> Rev;
            VRI.chain.clear();

            const Value *V = cur;
            while (V) {
                Rev.push_back(V);
                auto It = preds.find(V);
                if (It == preds.end()) break;
                V = It->second;
            }

            // reverse
            for (auto It = Rev.rbegin(); It != Rev.rend(); ++It) {
                if (!isa<BinaryOperator>(*It)) continue;
                VRI.chain.push_back(*It);
            }
            
            VRI.kind = VRAInspectionKind::REC; // ring found

            LLVM_DEBUG(tda::log() << "FOUND REC: " << VRI.chainToString());
            return;
        }

        for (const User *U : cur->users()) {
            auto *I = dyn_cast<Instruction>(U);
            if (!I) continue;

            // list of plausible instruction which can continue the flow
            if (isa<CastInst>(I) || isa<BinaryOperator>(I) || isa<CallInst>(I) || VFI.RRs.count(I)) {
                enqueue(cur, I);
                continue;
            }
        }
    }

    LLVM_DEBUG(tda::log() << "closed-path not found. Aborted.\n");
    VRI.chain.clear();
}

void ModuleInterpreter::handleStoreChain(VRAFunctionInfo VFI, Loop* L, const StoreInst* Store, VRARecurrenceInfo& VRI) {

    VRI.chain.clear();
    VRI.kind = VRAInspectionKind::UNKNOWN;

    const Value* StoreValue = Store->getValueOperand();
    const Value* StoreBase = getBaseMemoryObject(Store->getPointerOperand());
    if (!StoreBase || !StoreValue) return;

    SmallVector<const Value*, 32> worklist;
    DenseMap<const Value*, const Value*> preds;
    auto enqueue = [&](const Value *from, const Value *to) {
        if (preds.contains(to)) return;
        preds[to] = from;
        worklist.push_back(to);
    };

    preds[Store] = nullptr;
    worklist.push_back(Store);

    while (!worklist.empty()) {
        const Value *cur = worklist.pop_back_val();

        if (auto Load = dyn_cast<LoadInst>(cur)) {
            const Value* LoadBase = getBaseMemoryObject(Load->getPointerOperand());
            
            if (StoreBase == LoadBase) {

                SmallVector<const Value*, 32> Rev;
                VRI.chain.clear();

                const Value *V = cur;
                while (V) {
                    Rev.push_back(V);
                    auto It = preds.find(V);
                    if (It == preds.end()) break;
                    V = It->second;
                }

                // reverse
                for (auto It = Rev.rbegin(); It != Rev.rend(); ++It) {
                    if (!isa<BinaryOperator>(*It)) continue;
                    VRI.chain.push_back(*It);
                }
                
                VRI.kind = VRAInspectionKind::REC; // ring found

                LLVM_DEBUG(tda::log() << "FOUND REC: " << VRI.chainToString());
                return;
            }

            continue;   // useless follow again load users
        }

        for (const User *U : cur->users()) {
            auto *I = dyn_cast<Instruction>(U);
            if (!I) continue;

            // list of plausible instruction which can continue the flow
            if (isa<LoadInst>(I) ||isa<CastInst>(I) || isa<BinaryOperator>(I) || isa<CallInst>(I) || VFI.RRs.count(I)) {
                enqueue(cur, I);
                continue;
            }
        }

    }
}

std::string VRARecurrenceInfo::chainToString() {
    std::string S;
    llvm::raw_string_ostream OS(S);
    
    auto printValueName = [&](const llvm::Value *V) {
        if (!V) return;
        if (!V->getName().empty()) { OS << V->getName(); }
        else { V->printAsOperand(OS, false); }
    };

    auto printBaseOp = [&](const llvm::Value *Ptr) {
        const llvm::Value *Base = getBaseMemoryObject(Ptr);
        if (Base) { printValueName(Base); }
        else { OS << "<unknown>"; }
    };

    auto printValue = [&](const llvm::Value *V) {
        if (!V) return;
        if (const auto *SI = llvm::dyn_cast<llvm::StoreInst>(V)) {
            OS << "store(";
            printBaseOp(SI->getPointerOperand());
            OS << ")";
            return;
        }
        if (const auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
            OS << "load(";
            printBaseOp(LI->getPointerOperand());
            OS << ")";
            return;
        }
        printValueName(V);
    };

    OS << "  flow: ";
    printValue(root);
    OS << " => ";

    for (unsigned i = 0; i < chain.size(); ++i) {
        const llvm::Value* V = chain[i];
        printValue(V);

        if (i + 1 < chain.size())
        OS << " => ";
    }

    if (kind == VRAInspectionKind::REC) {
        OS << " => ";
        printValueName(root);
        OS << " || RECURRENCE";
    } else if (kind == VRAInspectionKind::INIT) {
        OS << " || INITIALIZATION";
    } else {
        OS << " || UNKNOWN";
    }

    OS << "\n";

    return OS.str();
}



}
