#pragma once

#include "CodeInterpreter.hpp"
#include "VRAFunctionStore.hpp"
#include "VRAGlobalStore.hpp"
#include "VRALogger.hpp"
#include "VRAStore.hpp"

#include "ModuleInterpreter.hpp"

#define DEBUG_TYPE "taffo-vra"

namespace taffo {

class VRAnalyzer : protected VRAStore,
                   public CodeAnalyzer {
public:
  VRAnalyzer(std::shared_ptr<VRALogger> VRAL, CodeInterpreter* CI)
  : VRAStore(VRASK_VRAnalyzer, VRAL), CodeAnalyzer(ASK_VRAnalyzer), CodeInt(CI), ModInt(nullptr) {}
  VRAnalyzer(std::shared_ptr<VRALogger> VRAL, ModuleInterpreter* MI)
  : VRAStore(VRASK_VRAnalyzer, VRAL), CodeAnalyzer(ASK_VRAnalyzer), CodeInt(nullptr), ModInt(MI) {}

  using VRAStore::saveValueRange;

  void convexMerge(const AnalysisStore& other) override;
  std::shared_ptr<CodeAnalyzer> newCodeAnalyzer(CodeInterpreter& CI) override;
  std::shared_ptr<AnalysisStore> newFunctionStore(CodeInterpreter& CI) override;
  std::shared_ptr<CodeAnalyzer> newInstructionAnalyzer(ModuleInterpreter& MI) override;
  std::shared_ptr<AnalysisStore> newFnStore(ModuleInterpreter& MI) override;

  bool hasValue(const llvm::Value* V) const override {
    auto It = DerivedRanges.find(V);
    return It != DerivedRanges.end() && It->second;
  }

  std::shared_ptr<CILogger> getLogger() const override { return Logger; }
  std::shared_ptr<CodeAnalyzer> clone() override;

  void analyzeInstruction(llvm::Instruction* I) override;
  void analyzePHIStartInstruction(llvm::Instruction* I) override;
  void resolveRecurrence(VRARecurrenceInfo& VRI, unsigned TripCount) override;
  void retrieveSolvedRecurrence(llvm::Instruction* I, VRARecurrenceInfo& VRI) override;
  void setPathLocalInfo(std::shared_ptr<CodeAnalyzer> SuccAnalyzer, llvm::Instruction* TermInstr, unsigned SuccIdx) override;
  bool requiresInterpretation(llvm::Instruction* I) const override;
  void prepareForCall(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore) override;
  void returnFromCall(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore) override;

  void prepareForCallPropagation(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore) override;
  void returnFromCallPropagation(llvm::Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore) override;

  std::shared_ptr<Range>getRange(const std::shared_ptr<ValueInfo> Range);
  std::shared_ptr<Range>getBBRange(const llvm::Value *V);
  std::shared_ptr<Range> getRRJoinedRange(RangedRecurrence* RR, u_int64_t TC);

  void fallbackCMP(const llvm::Instruction* I);

  //affine standard
  std::shared_ptr<RangedRecurrence> buildAffinePHIRecurrence(const llvm::PHINode *phi) override;
  std::shared_ptr<RangedRecurrence> buildAffineStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst*phi) override;
  
  std::shared_ptr<RangedRecurrence> buildFakeStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst*phi) override;

  // flattened
  std::shared_ptr<RangedRecurrence> buildPHIAffineFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::PHINode* phi) override;
  std::shared_ptr<RangedRecurrence> buildAffineFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* store) override;
  std::shared_ptr<RangedRecurrence> buildPHIGeometricFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::PHINode* phi) override;
  std::shared_ptr<RangedRecurrence> buildGeometricFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* store) override;

  //delta
  std::shared_ptr<RangedRecurrence> buildDeltaAffinePHIRecurrence(VRARecurrenceInfo VRI, const llvm::PHINode* store, VRARecurrenceInfo* InnerVRI) override;
  std::shared_ptr<RangedRecurrence> buildDeltaAffineStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* store, VRARecurrenceInfo* InnerVRI) override;
  std::shared_ptr<RangedRecurrence> buildDeltaGeometricPHIRecurrence(VRARecurrenceInfo VRI, const llvm::PHINode* store, VRARecurrenceInfo* InnerVRI) override;
  std::shared_ptr<RangedRecurrence> buildDeltaGeometricStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* store, VRARecurrenceInfo* InnerVRI) override;

  //crossing
  std::pair<std::shared_ptr<RangedRecurrence>, std::shared_ptr<RangedRecurrence>> buildStoreCrossingAffineRecurrence(VRAAssignationInfo first, VRAAssignationInfo second) override;
  std::pair<std::shared_ptr<RangedRecurrence>, std::shared_ptr<RangedRecurrence>> buildStoreCrossingGeometricRecurrence(VRAAssignationInfo first, VRAAssignationInfo second) override;
  
  std::shared_ptr<RangedRecurrence> buildInitRecurrence(std::shared_ptr<Range> LastStoredRange, const llvm::StoreInst *store) override;
  std::shared_ptr<RangedRecurrence> buildUnknownRecurrence(const llvm::Value *V) override;
  std::shared_ptr<RangedRecurrence> buildGeometricPHIRecurrence(const llvm::PHINode *phi) override;
  std::shared_ptr<RangedRecurrence> buildGeometricStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst*phi) override;

  size_t compareLoadStoreDim(VRAFunctionInfo VFI, const llvm::Value *load, const llvm::Value *store) override;

  static bool classof(const AnalysisStore* AS) { return AS->getKind() == ASK_VRAnalyzer; }

  static bool classof(const VRAStore* VS) { return VS->getKind() == VRASK_VRAnalyzer; }

#ifdef UNITTESTS

public:
  std::shared_ptr<ValueInfo> getNode(const llvm::Value* v) override;
  void setNode(const llvm::Value* V, std::shared_ptr<ValueInfo> Node) override;
#else

private:
  std::shared_ptr<ValueInfo> getNode(const llvm::Value* v) override;
  void setNode(const llvm::Value* V, std::shared_ptr<ValueInfo> Node) override;
#endif

private:
  // Instruction Handlers
  void handleSpecialCall(const llvm::Instruction* I);
  void handleMemCpyIntrinsics(const llvm::Instruction* memcpy);
  bool isMallocLike(const llvm::Function* F) const;
  bool isCallocLike(const llvm::Function* F) const;
  void handleMallocCall(const llvm::CallBase* CB);
  bool detectAndHandleLibOMPCall(const llvm::CallBase* CB);

  void handleReturn(const llvm::Instruction* ret);

  void handleAllocaInstr(llvm::Instruction* I);
  void handleStoreInstr(const llvm::Instruction* store);
  void handleLoadInstr(llvm::Instruction* load);
  void handleGEPInstr(const llvm::Instruction* gep);
  void handleBitCastInstr(llvm::Instruction* I);

  void handleCmpInstr(const llvm::Instruction* cmp);
  void handlePhiNode(const llvm::Instruction* phi);
  void handleSelect(const llvm::Instruction* i);

  // Data handling
  using VRAStore::fetchRange;
  std::shared_ptr<Range> fetchRange(const llvm::Value* v) override;
  std::shared_ptr<ValueInfoWithRange> fetchRangeNode(const llvm::Value* v) override;

  // Interface with CodeInterpreter
  std::shared_ptr<VRAGlobalStore> getGlobalStore() const {
    return CodeInt ? std::static_ptr_cast<VRAGlobalStore>(CodeInt->getGlobalStore()) : std::static_ptr_cast<VRAGlobalStore>(ModInt->getGlobalStore());
  }

  std::shared_ptr<VRAStore> getAnalysisStoreForValue(const llvm::Value* V) const {
    std::shared_ptr<AnalysisStore> AStore = CodeInt ? CodeInt->getStoreForValue(V) : ModInt->getStoreForValue(V);
    if (!AStore)
      return nullptr;

    // Since llvm::dyn_cast<T>() does not do cross-casting, we must do this:
    if (std::shared_ptr<VRAnalyzer> VRA = std::dynamic_ptr_cast<VRAnalyzer>(AStore))
      return std::static_ptr_cast<VRAStore>(VRA);
    else if (std::shared_ptr<VRAGlobalStore> VRAGS = std::dynamic_ptr_cast<VRAGlobalStore>(AStore))
      return std::static_ptr_cast<VRAStore>(VRAGS);
    else if (std::shared_ptr<VRAFunctionStore> VRAFS = std::dynamic_ptr_cast<VRAFunctionStore>(AStore))
      return std::static_ptr_cast<VRAStore>(VRAFS);
    return nullptr;
  }

  // Logging
  void logRangeln(const llvm::Value* v);

  CodeInterpreter* CodeInt;
  ModuleInterpreter* ModInt;
};

} // end namespace taffo

#undef DEBUG_TYPE
