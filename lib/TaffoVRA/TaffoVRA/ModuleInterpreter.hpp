#pragma once
#include "CodeInterpreter.hpp"
#include "VRALogger.hpp"
#include "RangedRecurrences.hpp"

#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/ScalarEvolution.h>
#include <memory>

namespace taffo {

class Range;

enum FollowingPathResponse {
    ENQUE_BLOCK, NO_ENQUE, LOOP_JOIN, LOOP_FORK
};

struct VRALoopInfo {
    llvm::Loop* L;
    u_int64_t TripCount;
    llvm::Value* InductionVariable;

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

    llvm::SmallVector<llvm::Function*> depsOnFn;
    llvm::SmallVector<llvm::Value*> depsOnRR;

    llvm::DenseMap<const llvm::Value*, std::shared_ptr<RangedRecurrence>> RRs;
    std::shared_ptr<Range> lastRange;
    u_int64_t lastRangeComputedAt = 0;

    VRARecurrenceInfo(const llvm::Value* root): root(root) {}
    bool isValid() { return chain.size() > 0; }
    std::string chainToString();
};

struct VRAFunctionInfo {
    llvm::Function* F;
    llvm::SmallVector<llvm::BasicBlock*> bbFlow;
    llvm::DenseMap<const llvm::Loop*, VRALoopInfo> loops;
    llvm::DenseMap<const llvm::Value*, VRARecurrenceInfo> RRs;
    FunctionScope scope;

    std::shared_ptr<Range> lastRange;
    llvm::DenseMap<llvm::Argument*, Range> lastRangeArgs;

    llvm::DominatorTree* DT;
    llvm::LoopInfo* LI;
    llvm::ScalarEvolution* SE;

    VRAFunctionInfo(): F(nullptr) {}
    VRAFunctionInfo(llvm::Function* F, llvm::ModuleAnalysisManager& MAM): F(F) {
        auto& FAM = MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(*F->getParent()).getManager();
        LI = &(FAM.getResult<llvm::LoopAnalysis>(*F));
        DT = &(FAM.getResult<llvm::DominatorTreeAnalysis>(*F));
        SE = &(FAM.getResult<llvm::ScalarEvolutionAnalysis>(*F));

        //todo: argument handlers??
    }

    size_t countLoops() { return loops.size(); }
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

    ModuleInterpreter(llvm::Module& M, llvm::ModuleAnalysisManager& MAM, std::shared_ptr<AnalysisStore> GlobalStore): M(M), GlobalStore(GlobalStore), curFn(), MAM(MAM), FNs() {}

protected:

    // 1) PRESEED METHODS
    void preSeed();
    void interpretFunction(llvm::Function* F, std::shared_ptr<AnalysisStore> FunctionStore = nullptr);
    FollowingPathResponse followPath(VRAFunctionInfo info, llvm::BasicBlock* src, llvm::BasicBlock* dst, llvm::SmallVector<llvm::Loop*> nesting) const;
    void interpretCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I);
    void updateSuccessorAnalyzer(std::shared_ptr<CodeAnalyzer> CurrentAnalyzer, llvm::Instruction* TermInstr, unsigned SuccIdx);

    // 2) INSPECTION PHASE METHODS
    void inspect();
    bool isInductionVariable(llvm::Function *F, llvm::Loop* L, const llvm::PHINode* PHI);
    void handlePHIChain(VRAFunctionInfo VFI, llvm::Loop* L, const llvm::PHINode* PHI, VRARecurrenceInfo& VRI);
    void handleStoreChain(VRAFunctionInfo VFI, llvm::Loop* L, const llvm::StoreInst* Store, VRARecurrenceInfo& VRI);

    // 3) ASSEMBLING METHODS
    void assemble();
    bool isFakeRecurrence(VRARecurrenceInfo& VRI);
    bool isAffineRecurrence(VRARecurrenceInfo& VRI);
    bool isDeltaAffineRecurrence(VRARecurrenceInfo& VRI);
    bool isGeometricRecurrence(VRARecurrenceInfo& VRI);
    bool isDeltaGeometricRecurrence(VRARecurrenceInfo& VRI);
    void fallbackRecurrence(VRARecurrenceInfo& VRI);
    // add here new recurrences...

    // 4) TRIP COUNT METHODS
    void tripCount();

    // 5) PROPAGATION METHODS
    void propagate();




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

    llvm::DenseMap<llvm::Function*, VRAFunctionInfo> FNs;

};

}
