#pragma once
#include "CodeInterpreter.hpp"
#include "VRALogger.hpp"
#include "RangedRecurrences.hpp"

#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/MemorySSA.h>

#include <memory>
#define DEBUG_TYPE "taffo-vra"
namespace taffo {

class Range;
class VRAGlobalStore;

enum FollowingPathResponse {
    ENQUE_BLOCK, NO_ENQUE, LOOP_JOIN, LOOP_FORK
};

enum class TripCountReason {
    Unknown = 0,
    DeducedBySCEV,
    HeuristicFallback
    // (slot futuri) UserHint, BoundedByGuard, ecc.
};

struct VRALoopInfo {
    llvm::Loop* L;
    u_int64_t TripCount = 0;
    TripCountReason Reason = TripCountReason::Unknown;
    llvm::Value* InductionVariable;
    llvm::CmpInst* exitCmp = nullptr;

    llvm::SmallVector<llvm::BasicBlock*> bbFlow;

    bool isInvariant(const llvm::Value* V) { return L->isLoopInvariant(V); }

    /// @brief check if all blocks of the loop are visited
    /// @return true is whole visited (all latches are visited), false otherwise
    bool isEntirelyVisited() {
        llvm::SmallVector<llvm::BasicBlock*, 4> latches;
        L->getLoopLatches(latches);
        
        for (auto latch : latches) {
            if (std::find(bbFlow.begin(), bbFlow.end(), latch) == bbFlow.end()) return false;
        }
        return true;
    }

    VRALoopInfo() : L(nullptr) {}
    VRALoopInfo(llvm::Loop* L) : L(L) {}
};

enum VRAInspectionKind {
    REC,        // known recurrence
    INIT,       // initialization
    UNKNOWN     // unhandled
};

struct VRARecurrenceInfo {
    const llvm::Value* root;
    llvm::SmallVector<const llvm::Value*> chain;
    VRAInspectionKind kind;
    const llvm::LoadInst* loadJunction = nullptr;
    const llvm::LoadInst* loadHigherDim = nullptr;

    llvm::SmallVector<llvm::Function*> depsOnFn;
    llvm::SmallVector<llvm::Value*> depsOnRR;

    std::shared_ptr<RangedRecurrence> RR = nullptr;
    std::shared_ptr<Range> lastRange = nullptr;
    u_int64_t lastRangeComputedAt = 0;

    VRARecurrenceInfo(): root(nullptr) {}
    VRARecurrenceInfo(const llvm::Value* root): root(root) {}
    bool isValid() { return chain.size() > 0; }
    std::string chainToString();
};

struct VRAFunctionInfo {
    llvm::Function* F;
    llvm::SmallVector<llvm::BasicBlock*> bbFlow;
    llvm::DenseMap<const llvm::Loop*, VRALoopInfo> loops;
    llvm::DenseMap<const llvm::Value*, VRARecurrenceInfo> RRs;
    llvm::DenseMap<const llvm::Value*, unsigned> RRs_pos;
    FunctionScope scope;

    std::shared_ptr<Range> lastRange;
    llvm::DenseMap<llvm::Value*, std::shared_ptr<Range>> lastRangeArgs;

    llvm::DominatorTree* DT = nullptr;
    llvm::LoopInfo* LI = nullptr;
    llvm::ScalarEvolution* SE = nullptr;
    llvm::MemorySSA* MSSA = nullptr;

    VRAFunctionInfo(): F(nullptr) {}
    VRAFunctionInfo(llvm::Function* F, llvm::ModuleAnalysisManager& MAM): F(F) {
        auto& FAM = MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(*F->getParent()).getManager();
        LI = &(FAM.getResult<llvm::LoopAnalysis>(*F));
        DT = &(FAM.getResult<llvm::DominatorTreeAnalysis>(*F));
        SE = &(FAM.getResult<llvm::ScalarEvolutionAnalysis>(*F));
        MSSA = &(FAM.getResult<llvm::MemorySSAAnalysis>(*F).getMSSA());
    }

    void addRecurrenceInfo(VRARecurrenceInfo RI) {
        RRs.try_emplace(RI.root, RI);
        RRs_pos.try_emplace(RI.root, RRs.size());
    }

    bool isRRBefore(const llvm::Value *V1, const llvm::Value *V2) const {
        auto I1 = RRs_pos.find(V1);
        auto I2 = RRs_pos.find(V2);

        if (I1 == RRs_pos.end() || I2 == RRs_pos.end())
            return false;

        return I1->second < I2->second;
    }

    size_t countLoops() { return loops.size(); }
    bool existAtLeastOneLoopWithoutTripCount() {
        for (auto [_, loop] : loops) {
            if (loop.TripCount == 0) return true;
        }
        return false;
    }
};

class ModuleInterpreter {
public:

    std::shared_ptr<AnalysisStore> getStoreForValue(const llvm::Value* V) const;
    std::shared_ptr<AnalysisStore> getGlobalStore() const { return GlobalStore; }
    std::shared_ptr<AnalysisStore> getFunctionStore() const {
        if (curFn.empty())
            return nullptr;
        auto It = FNs.find(curFn.back());
        if (It == FNs.end())
            return nullptr;
        return It->second.scope.FunctionStore;
    }
    llvm::ModuleAnalysisManager& getMAM() const { return MAM; }

    void interpret();

    // method to embed fixed-point loop and avoid recall preseed and inspect
    void resolve();

    ModuleInterpreter(llvm::Module& M, llvm::ModuleAnalysisManager& MAM, std::shared_ptr<AnalysisStore> GlobalStore);

protected:

    // 1) PRESEED METHODS
    void preSeed();
    void interpretFunction(llvm::Function* F, std::shared_ptr<AnalysisStore> FunctionStore = nullptr);
    FollowingPathResponse followPath(VRAFunctionInfo info, llvm::BasicBlock* src, llvm::BasicBlock* dst, llvm::SmallVector<llvm::Loop*> nesting) const;
    void interpretCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I, bool& isRangeChanged);
    
    void updateSuccessorAnalyzer(std::shared_ptr<CodeAnalyzer> CurrentAnalyzer, llvm::Instruction* TermInstr, unsigned SuccIdx);

    // 2) INSPECTION PHASE METHODS
    void inspect();
    bool isInductionVariable(llvm::Function *F, llvm::Loop* L, const llvm::PHINode* PHI);
    void handlePHIChain(VRAFunctionInfo VFI, llvm::Loop* L, const llvm::PHINode* PHI, VRARecurrenceInfo& VRI);
    void handleStoreChain(VRAFunctionInfo VFI, llvm::Loop* L, const llvm::StoreInst* Store, VRARecurrenceInfo& VRI);

    // LATTEX - RESOLUTION METHODS
    void resolveFunction(llvm::Function* F, std::shared_ptr<AnalysisStore> FunctionStore = nullptr);
    void resolveCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I, bool& isRangeChanged);
    
    // 3) ASSEMBLING METHODS
    void assemble();

    bool analyzeSolvability(const llvm::Value* cur, VRAFunctionInfo& VFI, VRARecurrenceInfo& VRI, VRALoopInfo& VLI);
    bool isSolvableDependenceTree(const llvm::Value *V, llvm::Loop* L, VRARecurrenceInfo& VRI);
    bool isSolvableDependenceTreeBackwark(const llvm::Value *V, llvm::Loop* L, VRARecurrenceInfo& VRI);
    void updateKnownSuccessorAnalyzer(std::shared_ptr<CodeAnalyzer> CurrentAnalyzer, llvm::BasicBlock* nextBlock, llvm::Function* F, FunctionScope& FS);

    bool isFakeRecurrence(VRARecurrenceInfo& VRI);
    bool isUnknownRecurrence(VRARecurrenceInfo& VRI);
    bool isInitRecurrence(VRARecurrenceInfo& VRI);
    bool isAffineRecurrence(VRARecurrenceInfo& VRI);
    bool isDeltaAffineRecurrence(VRARecurrenceInfo& VRI);
    bool isGeometricRecurrence(VRARecurrenceInfo& VRI);
    bool isDeltaGeometricRecurrence(VRARecurrenceInfo& VRI);
    bool isCrossingAffineRecurrence(VRARecurrenceInfo& VRI);
    void fallbackRecurrence(VRARecurrenceInfo& VRI);
    // add here new recurrences...

    const llvm::Value* matchIVOffset(VRAFunctionInfo VFI, const llvm::Value *Idx, int64_t &Offset, llvm::Loop *L);

    // 4) TRIP COUNT METHODS
    void tripCount();
    bool existAtLeastOneLoopWithoutTripCount() {
        for (auto [_, FN] : FNs) {
            if (FN.existAtLeastOneLoopWithoutTripCount()) return true;
        }
        return false;
    }

    // 5) PROPAGATION METHODS
    void propagate();
    void propagateFunction(llvm::Function* F);
    void walk(llvm::Loop* L = nullptr);

    // resolve all locked loops and RR after last iteration and iterate one again
    void fallback();
    void fallbackCMP();

    // Statistic methods
    size_t countLoops() {
        size_t num_loops = 0;
        for (auto [F, VFI] : FNs) {
            num_loops += VFI.countLoops();
        }
        return num_loops;
    }

    size_t countPotentialRecurrences() {
        size_t num_rr = 0;
        for (auto [F, VFI] : FNs) {
            num_rr += VFI.RRs.size();
        }
        return num_rr;
    }

private:

    llvm::Module& M;
    std::shared_ptr<AnalysisStore> GlobalStore;
    llvm::SmallVector<llvm::Function*, 4U> curFn;    //current function scope
    llvm::ModuleAnalysisManager& MAM;

    llvm::Function* EntryFn = nullptr;
    llvm::DenseMap<llvm::Function*, VRAFunctionInfo> FNs;

    llvm::SmallVector<const llvm::Value*> solvedRR;
    u_int16_t solvedTC;
    u_int64_t propagationChanging;
};

}
