#include "ValueRangeAnalysisPass.hpp"
#include "ModuleInterpreter.hpp"
#include "TaffoInfo/TaffoInfo.hpp"
#include "VRAFunctionStore.hpp"
#include "VRAGlobalStore.hpp"
#include "VRAnalyzer.hpp"

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

ModuleInterpreter::ModuleInterpreter(llvm::Module& M, llvm::ModuleAnalysisManager& MAM, std::shared_ptr<AnalysisStore> GlobalStore): 
    M(M), GlobalStore(GlobalStore), curFn(), MAM(MAM), FNs() {
        auto GS = std::static_pointer_cast<VRAGlobalStore>(GlobalStore);
        if (GS)
            OriginalGlobalStore = GS->deepClone();
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

    resolve();
}

void ModuleInterpreter::resolve() {
    size_t iteration = 1;
    //size_t changes = 0;
    do {

        assemble();

        LLVM_DEBUG(tda::log() << "\n\n------------------------------------------------------------------------------\n");
        LLVM_DEBUG(tda::log() << "assembling iter "<<iteration<<" completed: solved " << solvedRR.size() << " recurrences.\n");
        LLVM_DEBUG(tda::log() <<   "------------------------------------------------------------------------------\n\n");

        if (existAtLeastOneLoopWithoutTripCount()) {
            tripCount();

            LLVM_DEBUG(tda::log() << "\n\n------------------------------------------------------------------------------\n");
            LLVM_DEBUG(tda::log() << "trip count iter " << iteration << " completed: found " << solvedTC << " trip count.\n");
            LLVM_DEBUG(tda::log() <<   "------------------------------------------------------------------------------\n\n");
        }

        propagate();

        LLVM_DEBUG(tda::log() << "\n\n------------------------------------------------------------------------------\n");
        LLVM_DEBUG(tda::log() << "propagation iter " << iteration << " completed: changing on " << propagationChanging << " instructions.\n");
        LLVM_DEBUG(tda::log() <<   "------------------------------------------------------------------------------\n\n");

        ++iteration;
        if (MaxPropagation && iteration > MaxPropagation) {
            LLVM_DEBUG(tda::log() << "Propagation interrupted: after " << MaxPropagation << " iteration(s) no fixed point reached\n");
            break;
        }
    } while (propagationChanging != 0);
}

//==================================================================================================
//======================= PRESEEDING METHODS =======================================================
//==================================================================================================

void ModuleInterpreter::preSeed() {

    for (Function& F : M) {
        if (!F.empty() && (TaffoInfo::getInstance().isStartingPoint(F)) && F.getName() == "main") {
            interpretFunction(&F);
            EntryFn = &F;
        }
    }

    if (!EntryFn) {
        LLVM_DEBUG(tda::log() << " No visitable functions found.\n");
    }

}

void ModuleInterpreter::interpretFunction(llvm::Function* F, std::shared_ptr<AnalysisStore> FunctionStore) {


    if (FNs.count(F) && FNs[F].bbFlow.size() > 0) {
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
        bool isRangeChanged = false;

        for (llvm::Instruction& I : *curBlock) {
            if (CurAnalyzer->requiresInterpretation(&I)) {
                interpretCall(CurAnalyzer, &I);
            } else {
                CurAnalyzer->analyzeInstruction(&I, isRangeChanged);
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
    GlobalStore->convexMerge(*FunctionStore);
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

void ModuleInterpreter::updateKnownSuccessorAnalyzer(std::shared_ptr<CodeAnalyzer> CurrentAnalyzer, llvm::BasicBlock* nextBlock, llvm::Function* F) {
    llvm::DenseMap<llvm::BasicBlock*, std::shared_ptr<CodeAnalyzer>>& BBAnalyzers = FNs[F].scope.BBAnalyzers;
    std::shared_ptr<CodeAnalyzer> SuccAnalyzer;
    auto SAIt = BBAnalyzers.find(nextBlock);
    if (SAIt == BBAnalyzers.end()) {
        SuccAnalyzer = CurrentAnalyzer->clone();
        BBAnalyzers[nextBlock] = SuccAnalyzer;
    }
    else {
        SuccAnalyzer = SAIt->second;
        SuccAnalyzer->convexMerge(*CurrentAnalyzer);
    }
}

void ModuleInterpreter::interpretCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I) {
    llvm::CallBase* CB = llvm::cast<llvm::CallBase>(I);
    llvm::Function* F = CB->getCalledFunction();
    if (!F || F->empty())
        return;

    std::shared_ptr<AnalysisStore> FunctionStore = GlobalStore->newFnStore(*this);

    CurAnalyzer->prepareForCall(I, FunctionStore, FNs[F]);
    interpretFunction(F, FunctionStore);
    CurAnalyzer->returnFromCall(I, FunctionStore, FNs[F]);
}

void ModuleInterpreter::resolveCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I, bool& isRangeChanged) {
    llvm::CallBase* CB = llvm::cast<llvm::CallBase>(I);
    llvm::Function* F = CB->getCalledFunction();
    if (!F || F->empty())
        return;

    std::shared_ptr<AnalysisStore> FunctionStore = FNs[F].scope.FunctionStore;

    CurAnalyzer->prepareForCallPropagation(I, FunctionStore, isRangeChanged, FNs[F]);
    if (isRangeChanged) {
        propagateFunction(F);
        CurAnalyzer->returnFromCallPropagation(I, FunctionStore, isRangeChanged, FNs[F]);
    } else {
        LLVM_DEBUG(tda::log() << "No arguments are widen, can reuse past range\n");
    }

}


//==================================================================================================
//======================= INSPECTION METHODS =======================================================
//==================================================================================================

void ModuleInterpreter::inspect() {

    for (auto &Entry : FNs) {
        llvm::Function *F = Entry.first;
        auto &VFI = Entry.second;
        if (VFI.loops.size() == 0) continue;

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

                    //add also unkowrn recurrence, for faster widening
                    VFI.RRs.try_emplace(static_cast<const llvm::Value*>(&I), VRI);
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

    LLVM_DEBUG(tda::log() << "UNNKONW REC: " << VRI.chainToString() << "\n");
    VRI.chain.clear();
}

void ModuleInterpreter::handleStoreChain(VRAFunctionInfo VFI, Loop* L, const StoreInst* Store, VRARecurrenceInfo& VRI) {

    VRI.chain.clear();
    VRI.kind = VRAInspectionKind::UNKNOWN;

    const Value* StoreValue = Store->getValueOperand();
    const Value* StoreBase = getBaseMemoryObject(Store->getPointerOperand());
    if (!StoreBase || !StoreValue) return;

    bool couldBeInit = false;
    SmallVector<const Value*, 32> worklist;
    DenseMap<const Value*, const Value*> preds;
    auto enqueue = [&](const Value *from, const Value *to) {
        if (preds.contains(to)) return;
        preds[to] = from;
        worklist.push_back(to);
    };

    preds[Store] = nullptr;
    worklist.push_back(StoreValue);

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

            couldBeInit = true;
            continue;   // useless follow again load users
        }

        if (auto callInstr = dyn_cast<CallInst>(cur)) {
            Type *retTy = callInstr->getType();
            couldBeInit = !retTy->isVoidTy();
            continue;
        }

        for (const User *U : cur->users()) {
            auto *I = dyn_cast<Instruction>(U);
            if (!I) continue;

            // list of plausible instruction which can continue the flow
            if (isa<LoadInst>(I) || isa<CastInst>(I) || isa<BinaryOperator>(I) || isa<CallInst>(I) || VFI.RRs.count(I)) {
                LLVM_DEBUG(tda::log() << " equeuing: "<<U->getName() << " from: " << I->getName() << " || ");
                enqueue(cur, I);
                continue;
            }
        }
    }

    // todo: other operands can bring to init instead of unknown
    if (couldBeInit) {
        VRI.kind = VRAInspectionKind::INIT;
        LLVM_DEBUG(tda::log() << "FOUND INIT: " << VRI.chainToString());
    } else {
        LLVM_DEBUG(tda::log() << "UNNKONW REC: " << VRI.chainToString());
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

//==================================================================================================
//======================= ASSEMBLING METHODS =======================================================
//==================================================================================================

void ModuleInterpreter::assemble() {
    solvedRR.clear();

    for (auto &Entry : FNs) {
        llvm::Function *F = Entry.first;
        auto &VFI = Entry.second;


        for (auto &RREntry : VFI.RRs) {
            const llvm::Value* root = RREntry.first;
            auto &VRI = RREntry.second;

            if (VRI.RR) continue;   //already solved

            LLVM_DEBUG(tda::log() << "[VRA] >> [ASSEMBLE] >> FN["<<F->getName()<<"] - Recognization of " << root->getName() << "\n");

            if (isUnknownRecurrence(VRI)) {

                solvedRR.push_back(root);
                continue;

            } else if (isAffineRecurrence(VRI)) {
                solvedRR.push_back(root);
                continue;
            }




        }
    }
}


bool ModuleInterpreter::isSolvableDependenceTree(const llvm::Value *V, llvm::Loop* L, VRARecurrenceInfo& VRI) {
    if (!V || !L) return false;

    if (V == VRI.root) return true;

    auto I = dyn_cast<Instruction>(V);
    if (!I) return false;
    llvm::Function* F = const_cast<llvm::Function*>(I->getParent()->getParent());
    VRAFunctionInfo& VFI = FNs[F];
    VRALoopInfo& VLI = FNs[F].loops[L];

    SmallVector<const Value*, 32> worklist;
    DenseMap<const Value*, const Value*> preds;
    auto enqueue = [&](const Value *from, const Value *to) {
        if (preds.contains(to)) return;
        preds[to] = from;
        worklist.push_back(to);
    };

    preds[V] = nullptr;
    worklist.push_back(V);

    while (!worklist.empty()) {
        const Value *cur = worklist.pop_back_val();

        //controllo invarianza

        if (auto CB = dyn_cast<CallBase>(I)) {
            // check invarianza di tutti gli argomenti

            if (!VLI.isInvariant(I)) {

                bool atLeastOneUnsolvedArg = false;
                for (const Use &Arg : CB->args()) {
                    const llvm::Value *ArgV = Arg.get();
                    if (VLI.isInvariant(ArgV))
                        continue;

                    if (VFI.RRs.count(ArgV) && !VFI.RRs[ArgV].RR) {
                        atLeastOneUnsolvedArg = true;
                    }
                }

                if (atLeastOneUnsolvedArg) {
                    VRI.depsOnFn.push_back(CB->getCalledFunction());
                    return false;
                } else {
                    VRI.depsOnFn.clear();
                }
            } else {
                LLVM_DEBUG(tda::log() << " operando call invariante, posso usare il suo range ");
            }

        }

        else if (!VLI.isInvariant(cur)) {

            if (VFI.RRs.count(cur) && VFI.RRs[cur].RR) {
                continue;
            }
            VRI.depsOnRR.push_back(const_cast<llvm::Value*>(cur));
            return false;
        }

        for (const User *U : cur->users()) {
            auto *I = dyn_cast<Instruction>(U);
            if (!I) continue;

            // list of plausible instruction which can continue the flow
            if (isa<LoadInst>(I) || isa<CastInst>(I) || isa<BinaryOperator>(I) || isa<CallInst>(I) || VFI.RRs.count(I)) {
                enqueue(cur, I);
                continue;
            }
        }
    }

    return true;
}

bool ModuleInterpreter::isUnknownRecurrence(VRARecurrenceInfo& VRI) {
    if (VRI.kind != VRAInspectionKind::UNKNOWN) return false;
    LLVM_DEBUG(tda::log() << "\t\ttry to recognize as unknown recurrence... \n");

    // se lo start è loopInvariant usalo e bona
    // se è loop variant controlla se è stato risolto
    // se non è stato risolto aspetta e aggiungi dipendenza

    // Cerca prima nello scope della funzione, poi nel global

    auto AStore = getStoreForValue(VRI.root);
    auto GStore = std::static_pointer_cast<VRAGlobalStore>(GlobalStore);
    std::shared_ptr<Range> StartRange;

    // // usa il global
    // if (AStore) {
    //     if (AStore->getKind() == AnalysisStore::AnalysisStoreKind::ASK_VRAFunctionStore) {
    //         auto Store = std::static_pointer_cast<VRAFunctionStore>(AStore);
    //         StartRange = Store->fetchRange(VRI.root);
    //     }
    //     if (AStore->getKind() == AnalysisStore::AnalysisStoreKind::ASK_VRAnalyzer) {
    //         auto Store = std::static_pointer_cast<VRAnalyzer>(AStore);
    //         StartRange = Store->fetchRange(VRI.root);
    //     }
    // } else {
        StartRange = GStore->fetchRange(VRI.root);
    //}

    if (!StartRange) StartRange = Range::Top().clone();

    auto StepRange = Range::Top().clone();

    LLVM_DEBUG(tda::log() << "\t\t\trecognized unknown(start= " << StartRange->toString() << ", step= " << StepRange->toString() << ")\n\n");
    VRI.RR = std::make_shared<FakeRangedRecurrence>(StartRange->clone(), StepRange->clone());
    return true;
}

static bool isAffineBinaryOp(const Value* V) {
    const auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
    if (!BO) return false;

    const unsigned opc = BO->getOpcode();
    return opc == llvm::Instruction::Add || opc == llvm::Instruction::Sub || opc == llvm::Instruction::FAdd || opc == llvm::Instruction::FSub;
}

static std::optional<double> getConstantAsDouble(const llvm::Value *V) {
    if (const auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
        return CI->getValue().roundToDouble();
    if (const auto *CF = llvm::dyn_cast<llvm::ConstantFP>(V))
        return CF->getValueAPF().convertToDouble();
    return std::nullopt;
}

bool ModuleInterpreter::isAffineRecurrence(VRARecurrenceInfo& VRI) {
    if (VRI.kind != VRAInspectionKind::REC) return false;
    LLVM_DEBUG(tda::log() << "\t\ttry to recognize as affine recurrence... \n");

    auto GStore = std::static_pointer_cast<VRAGlobalStore>(GlobalStore)->deepClone();
    const auto* InstrRoot = llvm::dyn_cast<llvm::Instruction>(VRI.root);
    llvm::Function* F = const_cast<llvm::Function*>(InstrRoot->getParent()->getParent());
    VRAFunctionInfo &VFI = FNs[F];
    llvm::Loop *L = VFI.LI->getLoopFor(InstrRoot->getParent());
    VRALoopInfo &VLI = VFI.loops[L];
    
    bool isSolvable = VRI.chain.size() > 0;
    for (const auto* RRNode : VRI.chain) {
        if (!isAffineBinaryOp(RRNode)) return false;
        const auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(RRNode);

        isSolvable &= isSolvableDependenceTree(BO->getOperand(0), L, VRI) && isSolvableDependenceTree(BO->getOperand(1), L, VRI);
    }
    
    // run every block of the current loop
    for (auto it = VLI.bbFlow.begin(); it != VLI.bbFlow.end(); ++it) {
        const llvm::BasicBlock *curBlock = *it;
        LLVM_DEBUG(tda::log() << "\nAnalysing block " << curBlock->getName() << " \n----------------------------------\n");
        
        auto CAIt = VFI.scope.BBAnalyzers.find(curBlock);
        assert(CAIt != VFI.scope.BBAnalyzers.end());
        std::shared_ptr<CodeAnalyzer> CurAnalyzer = CAIt->second;

        bool isRangeChanged = false;
        if (VFI.LI->getLoopFor(curBlock) == L) {
            for (const llvm::Instruction& CI : *curBlock) {
                llvm::Instruction &I = const_cast<llvm::Instruction &>(CI);
                if (CurAnalyzer->requiresInterpretation(&I)) {
                    resolveCall(CurAnalyzer, &I, isRangeChanged);
                } else {
                    // if (&I == const_cast<llvm::Instruction*>(InstrRoot)) {
                    if (isa<PHINode>(&I) && curBlock == L->getHeader()) {
                        CurAnalyzer->analyzePHIStartInstruction(&I);
                    } else {
                        CurAnalyzer->analyzeInstruction(&I, isRangeChanged);
                    }
                }
            }
        }

        const llvm::BasicBlock *nextBlock = nullptr;
        auto nextIt = std::next(it);
        if (nextIt != VLI.bbFlow.end())
            updateKnownSuccessorAnalyzer(CurAnalyzer, *nextIt, F);
        
        GStore->convexMerge(*CurAnalyzer);
    }
    
    std::shared_ptr<Range> StartRange = nullptr;
    std::shared_ptr<Range> StepRange = nullptr;
    if (const auto *PN = llvm::dyn_cast<llvm::PHINode>(VRI.root)) {
        StartRange = StepRange = GStore->fetchRange(VRI.root);
        const Value *latchIncoming = nullptr;
        if (auto *latch = L->getLoopLatch()) {
            latchIncoming = PN->getIncomingValueForBlock(latch);
            StepRange = handleSub(GStore->fetchRange(latchIncoming), StartRange);
        }
    }

    LLVM_DEBUG(tda::log() << "recognized affine(start= " << StartRange->toString() << ", step= " << StepRange->toString() << ")\n\n");
    VRI.RR = std::make_shared<AffineRangedRecurrence>(StartRange->clone(), std::move(StepRange));

    // LLVM_DEBUG(tda::log() << "[VRA][assemble] stored RR for root="
    //                   << VRI.root->getName()
    //                   << " ptr=" << (const void*)VRI.root << "\n\n\n");


    return true;
}

//==================================================================================================
//======================= TRIP COUNT METHODS =======================================================
//==================================================================================================

void ModuleInterpreter::tripCount() {
    solvedTC = 0;

    for (auto &Entry : FNs) {
        llvm::Function *F = Entry.first;
        auto &VFI = Entry.second;

        for (auto &LEntry : VFI.loops) {
            const llvm::Loop *L = LEntry.first;
            auto &VLI = LEntry.second;

            if (VLI.TripCount > 0) continue;

            //LLVM_DEBUG(tda::log() << " INDUCTION:  " << VLI.InductionVariable->getName() << " ptr=" << (const void*)VLI.InductionVariable << "\n");

            auto It = VFI.RRs.find(VLI.InductionVariable);
            if (It == VFI.RRs.end()) {
                LLVM_DEBUG(tda::log() << "[VRA][tripCount] RR entry NOT FOUND for IV " << VLI.InductionVariable->getName() << " ptr=" << (const void*)VLI.InductionVariable << "\n");
                continue;
            }

            auto &VRI = It->second;
            if (!VRI.RR) {
                LLVM_DEBUG(tda::log() << "[VRA][tripCount] RR entry found but RR==nullptr for IV " << VLI.InductionVariable->getName() << " ptr=" << (const void*)VLI.InductionVariable << "\n");
                continue;
            }

            if (auto *ARR = dyn_cast<AffineRangedRecurrence>(VRI.RR.get())) {
                const auto &Start = ARR->getStart();
                const auto &Step = ARR->getStep();
                if (!Start || !Step) continue;

                if (!VLI.exitCmp) {
                    //looking for block with exit successor, then get cmp with handle branch
                    for (auto BB : VLI.bbFlow) {
                        for (auto& I : *BB) {
                            if (auto BR = dyn_cast<BranchInst>(&I)) {
                                if (!BR->isConditional()) continue;
                                for (unsigned succ_idx = 0; succ_idx < BR->getNumSuccessors(); succ_idx++) {
                                    if (isLoopExit(L, BR->getSuccessor(succ_idx))) {
                                        auto cmp = BR->getCondition();
                                        // LLVM_DEBUG(tda::log() << " l'istruzione di uscita è " << cmp->getName() << "\n");
                                        VLI.exitCmp = dyn_cast<CmpInst>(cmp);
                                    }
                                }
                            }
                        }
                    }
                }

                if (!VLI.exitCmp) continue;

                CmpInst::Predicate Pred = VLI.exitCmp->getPredicate();
                llvm::Value* invariantOp;
                if (VLI.isInvariant(VLI.exitCmp->getOperand(0))) {
                    Pred = CmpInst::getSwappedPredicate(Pred);
                    invariantOp = VLI.exitCmp->getOperand(0);
                } else if (VLI.isInvariant(VLI.exitCmp->getOperand(1))) {
                    invariantOp = VLI.exitCmp->getOperand(1);
                } else continue;

                const bool isLT = Pred == CmpInst::ICMP_SLT || Pred == CmpInst::ICMP_ULT ||
                      Pred == CmpInst::FCMP_OLT || Pred == CmpInst::FCMP_ULT;
                const bool isLE = Pred == CmpInst::ICMP_SLE || Pred == CmpInst::ICMP_ULE ||
                                Pred == CmpInst::FCMP_OLE || Pred == CmpInst::FCMP_ULE;
                const bool isGT = Pred == CmpInst::ICMP_SGT || Pred == CmpInst::ICMP_UGT ||
                                Pred == CmpInst::FCMP_OGT || Pred == CmpInst::FCMP_UGT;
                const bool isGE = Pred == CmpInst::ICMP_SGE || Pred == CmpInst::ICMP_UGE ||
                                Pred == CmpInst::FCMP_OGE || Pred == CmpInst::FCMP_UGE;

                uint64_t TripC = 0;
                bool computed = false;

                auto GStore = std::static_pointer_cast<VRAGlobalStore>(GlobalStore);
                auto InvariantRange = GStore->fetchRange(invariantOp);
                //LLVM_DEBUG(tda::log() << " recuperato invariante " << invariantOp->getName() << " il cui range è "<<InvariantRange->toString()<<"\n");

                if ((isLT || isLE) && Step->min > 0.0) {
                    const double num = InvariantRange->max - Start->min;
                    const double den = Step->min;
                    if (den > 0.0 && std::isfinite(num)) {
                        TripC = static_cast<uint64_t>(std::ceil(num / den));
                        computed = true;
                    }
                } else if ((isGT || isGE) && Step->max < 0.0) {
                    const double num = Start->max - InvariantRange->min;
                    const double den = -Step->max;
                    if (den > 0.0 && std::isfinite(num)) {
                        TripC = static_cast<uint64_t>(std::ceil(num / den));
                        computed = true;
                    }
                } else {
                    LLVM_DEBUG(tda::log() << "todo: add here other heuristics\n");
                }

                if (computed) {
                    VLI.TripCount = TripC;
                    VLI.Reason = TripCountReason::HeuristicFallback;
                    LLVM_DEBUG(tda::log() << "trip count for loop " << VLI.L->getName() << " (affine growth) = " << TripC << "\n");
                    solvedTC++;
                }
            }

        }

    }
}

//==================================================================================================
//======================= PROPAGATE METHODS ========================================================
//==================================================================================================

void ModuleInterpreter::walk(llvm::Loop* L) {

    VRAFunctionInfo& VFI = FNs[curFn.back()];
    llvm::SmallVector<llvm::BasicBlock *> curFlow = L && FNs[curFn.back()].loops.count(L) ? FNs[curFn.back()].loops[L].bbFlow : FNs[curFn.back()].bbFlow;
    auto GStore = std::static_pointer_cast<VRAGlobalStore>(GlobalStore);


    for (auto it = curFlow.begin(); it != curFlow.end(); ++it) {
        const llvm::BasicBlock *curBlock = *it;
        llvm::Loop* curLoop = VFI.LI->getLoopFor(curBlock);

        if (!L && curLoop && curBlock == curLoop->getHeader() || L && curBlock == curLoop->getHeader() && L != curLoop) {
            walk(curLoop);
            continue;
        }

        LLVM_DEBUG({
            auto &dbg = tda::log();
            dbg << "\nPropagation over the function " << curFn.back()->getName();
            if (curLoop)
                dbg << ", loop " << curLoop->getName();
            dbg << ", block " << curBlock->getName() << " \n----------------------------------\n";
        });
    
        auto CAIt = VFI.scope.BBAnalyzers.find(curBlock);
        assert(CAIt != VFI.scope.BBAnalyzers.end());
        std::shared_ptr<CodeAnalyzer> CurAnalyzer = CAIt->second;

        for (const llvm::Instruction& CI : *curBlock) {
            llvm::Instruction &I = const_cast<llvm::Instruction &>(CI);

            auto OldRange = GStore->fetchRange(&I);
            bool isRangeChanged = false;

            // caso ricorrenza (conosciuta o non)
            if (FNs[curFn.back()].RRs.count(&I) && curLoop) {
                VRARecurrenceInfo& VRI = FNs[curFn.back()].RRs[&I];
                if (!VRI.RR) continue;
                CurAnalyzer->resolveRecurrence(VRI, FNs[curFn.back()].loops[curLoop].TripCount, isRangeChanged);
            } else if (CurAnalyzer->requiresInterpretation(&I)) {
                resolveCall(CurAnalyzer, &I, isRangeChanged);
            } else {
                CurAnalyzer->analyzeInstruction(&I, isRangeChanged);
            }

            if (isRangeChanged) {
                LLVM_DEBUG(tda::log() << " INSTRUCTION " << I.getName() << ": RANGE CHANGED\n");
                propagationChanging++;
            } 
        }
        
        const llvm::BasicBlock *nextBlock = nullptr;
        auto nextIt = std::next(it);
        if (nextIt != curFlow.end())
            updateKnownSuccessorAnalyzer(CurAnalyzer, *nextIt, curFn.back());
        
        GStore->convexMerge(*CurAnalyzer);
    }

}

void ModuleInterpreter::propagateFunction(llvm::Function* F) {

    VRAFunctionInfo& VFI = FNs[F];
    curFn.push_back(F);

    //scorriamo i bb della function, i suoi loop e le called. Se troviamo una root di RR lanciamola risolvendo la ricorrenza.
    walk();

    curFn.pop_back();
}

void ModuleInterpreter::propagate() {
    curFn.clear();
    propagationChanging = 0;
    propagateFunction(EntryFn);

}

}   // end of namespace taffo
