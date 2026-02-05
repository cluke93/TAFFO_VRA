#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/PassManager.h>

#define DEBUG_TYPE "taffo-vra"

namespace taffo {

class CodeInterpreter;
class CodeAnalyzer;
class ModuleInterpreter;
class VRARecurrenceInfo;
class VRAFunctionInfo;
class RangedRecurrence;
class Range;

class CILogger {
public:
  virtual const char* getDebugType() const = 0;
  virtual void logBasicBlock(const llvm::BasicBlock* BB) const = 0;
  virtual void logStartFunction(const llvm::Function* F) = 0;
  virtual void logEndFunction(const llvm::Function* F) = 0;
  virtual ~CILogger() = default;

  enum CILoggerKind {
    CILK_VRALogger
  };
  CILoggerKind getKind() const { return Kind; }

protected:
  CILogger(CILoggerKind K)
  : Kind(K) {}

private:
  CILoggerKind Kind;
};

class AnalysisStore {
public:
  virtual void convexMerge(const AnalysisStore& Other, bool isFallback = false) = 0;
  virtual std::shared_ptr<CodeAnalyzer> newCodeAnalyzer(CodeInterpreter& CI) = 0;
  virtual std::shared_ptr<AnalysisStore> newFunctionStore(CodeInterpreter& CI) = 0;

  virtual std::shared_ptr<CodeAnalyzer> newInstructionAnalyzer(ModuleInterpreter& FI) = 0;
  virtual std::shared_ptr<AnalysisStore> newFnStore(ModuleInterpreter& CI) = 0;

  virtual bool hasValue(const llvm::Value* V) const = 0;
  virtual std::shared_ptr<CILogger> getLogger() const = 0;
  virtual ~AnalysisStore() = default;

  enum AnalysisStoreKind {
    ASK_VRAGlobalStore,
    ASK_VRAnalyzer,
    ASK_VRAFunctionStore
  };
  AnalysisStoreKind getKind() const { return Kind; }

protected:
  AnalysisStore(AnalysisStoreKind K)
  : Kind(K) {}

private:
  const AnalysisStoreKind Kind;
};

class CodeAnalyzer : public AnalysisStore {
public:
  virtual std::shared_ptr<CodeAnalyzer> clone() = 0;
  virtual void analyzeInstruction(llvm::Instruction* I, bool& isRangeChanged) = 0;
  virtual void analyzePHIStartInstruction(llvm::Instruction* I, bool& isRangeChanged) = 0;
  virtual void retrieveSolvedRecurrence(llvm::Instruction* I, VRARecurrenceInfo& VRI, bool& isRangeChanged) = 0;
  virtual void resolveRecurrence(VRARecurrenceInfo& VRI, unsigned TripCount, bool& isRangeChanged) = 0;
  virtual void setPathLocalInfo(std::shared_ptr<CodeAnalyzer> SuccAnalyzer, llvm::Instruction* TermInstr, unsigned SuccIdx) = 0;
  virtual bool requiresInterpretation(llvm::Instruction* I) const = 0;
  virtual void prepareForCall(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, VRAFunctionInfo& VFI, bool& isRangeChanged) = 0;
  virtual void returnFromCall(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, VRAFunctionInfo& VFI, bool& isRangeChanged) = 0;

  virtual void prepareForCallPropagation(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, bool& isRangeChanged, VRAFunctionInfo& VFI) = 0;
  virtual void returnFromCallPropagation(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, bool& isRangeChanged, VRAFunctionInfo& VFI) = 0;

  virtual std::shared_ptr<RangedRecurrence> buildAffinePHIRecurrence(const llvm::PHINode *phi) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildAffineStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst*phi) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildFakeStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst*phi) = 0;

  virtual std::shared_ptr<RangedRecurrence> buildPHIAffineFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::PHINode* phi) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildAffineFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* store) = 0;

  virtual std::shared_ptr<RangedRecurrence> buildDeltaAffinePHIRecurrence(VRARecurrenceInfo VRI, const llvm::PHINode* phi, VRARecurrenceInfo* InnerVRI) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildDeltaAffineStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* store, VRARecurrenceInfo* InnerVRI) = 0;

  virtual std::shared_ptr<RangedRecurrence> buildInitRecurrence(std::shared_ptr<Range> LastStoredRange, const llvm::StoreInst *store) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildUnknownRecurrence(const llvm::Value *V) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildGeometricPHIRecurrence(const llvm::PHINode *phi) = 0;
  virtual std::shared_ptr<RangedRecurrence> buildGeometricStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst*phi) = 0;

  virtual size_t compareLoadStoreDim(VRAFunctionInfo VFI, const llvm::Value *load, const llvm::Value *store) = 0;

  static bool classof(const AnalysisStore* AS) {
    return AS->getKind() >= ASK_VRAGlobalStore && AS->getKind() <= ASK_VRAnalyzer;
  }

protected:
  CodeAnalyzer(AnalysisStoreKind K)
  : AnalysisStore(K) {}
};

struct FunctionScope {
  FunctionScope() {}
  FunctionScope(std::shared_ptr<AnalysisStore> FS) : FunctionStore(FS) {}

  std::shared_ptr<AnalysisStore> FunctionStore;
  llvm::DenseMap<llvm::BasicBlock*, std::shared_ptr<CodeAnalyzer>> BBAnalyzers;
  llvm::DenseMap<llvm::BasicBlock*, unsigned> EvalCount;
};

class CodeInterpreter {
public:
  CodeInterpreter(llvm::ModuleAnalysisManager& MAM,
                  std::shared_ptr<AnalysisStore> GlobalStore,
                  unsigned LoopUnrollCount = 1U,
                  unsigned LoopMaxUnrollCount = 256U)
  : GlobalStore(GlobalStore),
    Scopes(),
    MAM(MAM),
    LoopInfo(nullptr),
    LoopTripCount(),
    RecursionCount(),
    DefaultTripCount(LoopUnrollCount),
    MaxTripCount(LoopMaxUnrollCount) {}

  void interpretFunction(llvm::Function* F, std::shared_ptr<AnalysisStore> FunctionStore = nullptr);
  std::shared_ptr<AnalysisStore> getStoreForValue(const llvm::Value* V) const;

  std::shared_ptr<AnalysisStore> getGlobalStore() const { return GlobalStore; }
  std::shared_ptr<AnalysisStore> getFunctionStore() const { return Scopes.back().FunctionStore; }

  llvm::ModuleAnalysisManager& getMAM() const { return MAM; }

protected:
  std::shared_ptr<AnalysisStore> GlobalStore;
  llvm::SmallVector<FunctionScope, 4U> Scopes;
  llvm::ModuleAnalysisManager& MAM;
  llvm::LoopInfo* LoopInfo;
  llvm::DenseMap<llvm::BasicBlock*, unsigned> LoopTripCount;
  llvm::DenseMap<llvm::Function*, unsigned> RecursionCount;
  unsigned DefaultTripCount;
  unsigned MaxTripCount;

private:
  bool isLoopBackEdge(llvm::BasicBlock* Src, llvm::BasicBlock* Dst) const;
  llvm::Loop* getLoopForBackEdge(llvm::BasicBlock* Src, llvm::BasicBlock* Dst) const;
  bool followEdge(llvm::BasicBlock* Src, llvm::BasicBlock* Dst);
  void updateSuccessorAnalyzer(std::shared_ptr<CodeAnalyzer> CurrentAnalyzer,
                               llvm::Instruction* TermInstr,
                               unsigned SuccIdx);
  void interpretCall(std::shared_ptr<CodeAnalyzer> CurAnalyzer, llvm::Instruction* I);
  void updateLoopInfo(llvm::Function* F);
  void retrieveLoopTripCount(llvm::Function* F);
  bool updateRecursionCount(llvm::Function* F);
};

} // namespace taffo

#undef DEBUG_TYPE
