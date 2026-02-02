#include "MemSSAUtils.hpp"
#include "RangeOperations.hpp"
#include "TaffoInfo/TaffoInfo.hpp"
#include "Types/TypeUtils.hpp"
#include "VRAnalyzer.hpp"

#include <llvm/IR/Intrinsics.h>
#include <llvm/Support/Debug.h>

#include <llvm/Analysis/ValueTracking.h>
#include <llvm/Analysis/IVDescriptors.h>

using namespace llvm;
using namespace tda;
using namespace taffo;

#define DEBUG_TYPE "taffo-vra"

void VRAnalyzer::convexMerge(const AnalysisStore& other) {
  // Since dyn_cast<T>() does not do cross-casting, we must do this:
  if (isa<VRAnalyzer>(other))
    VRAStore::convexMerge(cast<VRAStore>(cast<VRAnalyzer>(other)));
  else if (isa<VRAGlobalStore>(other))
    VRAStore::convexMerge(cast<VRAStore>(cast<VRAGlobalStore>(other)));
  else
    VRAStore::convexMerge(cast<VRAStore>(cast<VRAFunctionStore>(other)));
}

std::shared_ptr<CodeAnalyzer> VRAnalyzer::newCodeAnalyzer(CodeInterpreter& CI) {
  return std::make_shared<VRAnalyzer>(std::static_ptr_cast<VRALogger>(CI.getGlobalStore()->getLogger()), &CI);
}

std::shared_ptr<AnalysisStore> VRAnalyzer::newFunctionStore(CodeInterpreter& CI) {
  return std::make_shared<VRAFunctionStore>(std::static_ptr_cast<VRALogger>(CI.getGlobalStore()->getLogger()));
}

std::shared_ptr<CodeAnalyzer> VRAnalyzer::newInstructionAnalyzer(ModuleInterpreter& MI) {
  return std::make_shared<VRAnalyzer>(std::static_ptr_cast<VRALogger>(MI.getGlobalStore()->getLogger()), &MI);
}

std::shared_ptr<AnalysisStore> VRAnalyzer::newFnStore(ModuleInterpreter& MI) {
  return std::make_shared<VRAFunctionStore>(std::static_ptr_cast<VRALogger>(MI.getGlobalStore()->getLogger()));
}

std::shared_ptr<CodeAnalyzer> VRAnalyzer::clone() { return std::make_shared<VRAnalyzer>(*this); }

std::shared_ptr<VRAnalyzer> VRAnalyzer::deepClone() const {
  auto clone = CodeInt ? std::make_shared<VRAnalyzer>(Logger, CodeInt)
                       : std::make_shared<VRAnalyzer>(Logger, ModInt);

  llvm::DenseMap<const ValueInfo*, std::shared_ptr<ValueInfo>> cache;
  cache.reserve(DerivedRanges.size());

  const auto cloneValue = [&](const std::shared_ptr<ValueInfo>& src) -> std::shared_ptr<ValueInfo> {
    if (!src)
      return nullptr;
    if (const auto it = cache.find(src.get()); it != cache.end())
      return it->second;
    auto copy = src->clone<ValueInfo>();
    cache[src.get()] = copy;
    return copy;
  };

  clone->DerivedRanges.reserve(DerivedRanges.size());
  for (const auto& [value, info] : DerivedRanges)
    clone->DerivedRanges[value] = cloneValue(info);

  return clone;
}

static const Value* stripCasts(const Value *V) {
    const Value *Cur = V;
    while (Cur) {
        if (auto *Cast = dyn_cast<CastInst>(Cur)) {
            Cur = Cast->getOperand(0);
            continue;
        }
        if (auto *CE = dyn_cast<ConstantExpr>(Cur)) {
            if (CE->isCast()) {
                Cur = CE->getOperand(0);
                continue;
            }
        }
        if (auto *Op = dyn_cast<Operator>(Cur)) {
            unsigned opc = Op->getOpcode();
            if (opc == Instruction::BitCast || opc == Instruction::AddrSpaceCast) {
                Cur = Op->getOperand(0);
                continue;
            }
        }
        break;
    }
    return Cur;
};

// return for load and stores its array dimension
static int getArrayAccessDimFromPtr(const Value *Ptr) {
  Ptr = stripCasts(Ptr);

  int dims = 0;
  const Value *Cur = Ptr;

  while (Cur) {
    Cur = stripCasts(Cur);

    const GEPOperator *GEP = dyn_cast<GEPOperator>(Cur);
    if (!GEP) break;

    Type *Ty = GEP->getSourceElementType();
    unsigned pos = 0;

    for (auto It = GEP->idx_begin(); It != GEP->idx_end(); ++It, ++pos) {
      if (pos == 0)
        continue;

      if (auto *Arr = dyn_cast<ArrayType>(Ty)) {
        ++dims;
        Ty = Arr->getElementType();
        continue;
      }

      if (auto *ST = dyn_cast<StructType>(Ty)) {
        if (auto *CI = dyn_cast<ConstantInt>(It->get())) {
          unsigned field = CI->getZExtValue();
          if (field < ST->getNumElements()) {
            Ty = ST->getElementType(field);
            continue;
          }
        }
        return -1;
      }
    }

    Cur = GEP->getPointerOperand();
  }

  return dims;
}

static bool isNewRangeWiden(const std::shared_ptr<Range> OldRange, const std::shared_ptr<Range> NewRange) {
  if (!OldRange && !NewRange) return false;
  if (!OldRange && NewRange || OldRange && !NewRange) return true;
  bool res = NewRange->min < OldRange->min || OldRange->max < NewRange->max;
  if (res) LLVM_DEBUG(tda::log()<< " RANGE WIDEN from " << OldRange->toString() << " to " << NewRange->toString() << "\n");
  return res;
};

void VRAnalyzer::analyzeInstruction(Instruction* I, bool& isRangeChanged) {
  assert(I);
  Instruction& i = *I;
  const unsigned OpCode = i.getOpcode();
  if (OpCode == Instruction::Call || OpCode == Instruction::Invoke) {
    handleSpecialCall(&i);
  }
  else if (Instruction::isCast(OpCode) && OpCode != Instruction::BitCast) {
    LLVM_DEBUG(Logger->logInstruction(&i));
    const Value* op = i.getOperand(0);
    const std::shared_ptr<Range> oldInfo = fetchRange(&i);
    const std::shared_ptr<Range> info = fetchRange(op);
    const std::shared_ptr<Range> res = handleCastInstruction(info, OpCode, i.getType());
    saveValueRange(&i, res);
    
    isRangeChanged = isNewRangeWiden(info, res);

    LLVM_DEBUG(
      if (!info)
        Logger->logInfo("operand range is null"));
    LLVM_DEBUG(logRangeln(&i));
  }
  else if (Instruction::isBinaryOp(OpCode)) {
    LLVM_DEBUG(Logger->logInstruction(&i));
    const Value* op1 = i.getOperand(0);
    const Value* op2 = i.getOperand(1);
    const std::shared_ptr<Range> oldInfo = fetchRange(&i);
    const std::shared_ptr<Range> info1 = fetchRange(op1);
    const std::shared_ptr<Range> info2 = fetchRange(op2);
    LLVM_DEBUG(tda::log() << " op1 range: " << (info1 ? info1->toString() : "null") << " op2: " << (info2 ? info2->toString() : "null"));
    const std::shared_ptr<Range> res = handleBinaryInstruction(info1, info2, OpCode);
    saveValueRange(&i, res);

    isRangeChanged = isNewRangeWiden(oldInfo, res);

    LLVM_DEBUG(
      if (!info1)
        Logger->logInfo("first range is null"));
    LLVM_DEBUG(
      if (!info2)
        Logger->logInfo("second range is null"));
    LLVM_DEBUG(logRangeln(&i));
  }
  else if (OpCode == Instruction::FNeg) {
    LLVM_DEBUG(Logger->logInstruction(&i));
    const Value* op1 = i.getOperand(0);
    const std::shared_ptr<Range> oldInfo = fetchRange(&i);
    const std::shared_ptr<Range> info1 = fetchRange(op1);
    const auto res = handleUnaryInstruction(info1, OpCode);
    saveValueRange(&i, res);

    isRangeChanged = isNewRangeWiden(oldInfo, res);

    LLVM_DEBUG(
      if (!info1)
        Logger->logInfo("operand range is null"));
    LLVM_DEBUG(logRangeln(&i));
  }
  else {
    switch (OpCode) {
    // memory operations
    case Instruction::Alloca:        handleAllocaInstr(I, isRangeChanged); break;
    case Instruction::Load:          handleLoadInstr(&i, isRangeChanged); break;
    case Instruction::Store:         handleStoreInstr(&i, isRangeChanged); break;
    case Instruction::GetElementPtr: handleGEPInstr(&i, isRangeChanged); break;
    case Instruction::BitCast:       handleBitCastInstr(I, isRangeChanged); break;
    case Instruction::Fence:
      LLVM_DEBUG(Logger->logErrorln("Handling of Fence not supported yet")); break; // TODO implement
    case Instruction::AtomicCmpXchg:
      LLVM_DEBUG(Logger->logErrorln("Handling of AtomicCmpXchg not supported yet"));
      break;                                                                                     // TODO implement
    case Instruction::AtomicRMW:
      LLVM_DEBUG(Logger->logErrorln("Handling of AtomicRMW not supported yet"));
      break;                                                                                     // TODO implement

      // other operations
    case Instruction::Ret: handleReturn(I, isRangeChanged); break;
    case Instruction::Br:
      // do nothing
      break;
    case Instruction::ICmp:
    case Instruction::FCmp:   handleCmpInstr(&i, isRangeChanged); break;
    case Instruction::PHI:    handlePhiNode(&i, isRangeChanged); break;
    case Instruction::Select: handleSelect(&i, isRangeChanged); break;
    case Instruction::UserOp1: // TODO implement
    case Instruction::UserOp2: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of UserOp not supported yet"));
      break;
    case Instruction::VAArg: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of VAArg not supported yet"));
      break;
    case Instruction::ExtractElement: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of ExtractElement not supported yet"));
      break;
    case Instruction::InsertElement: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of InsertElement not supported yet"));
      break;
    case Instruction::ShuffleVector: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of ShuffleVector not supported yet"));
      break;
    case Instruction::ExtractValue: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of ExtractValue not supported yet"));
      break;
    case Instruction::InsertValue: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of InsertValue not supported yet"));
      break;
    case Instruction::LandingPad: // TODO implement
      LLVM_DEBUG(Logger->logErrorln("Handling of LandingPad not supported yet"));
      break;
    default: LLVM_DEBUG(Logger->logErrorln("unhandled instruction " + std::to_string(OpCode))); break;
    }
  } // end else
}

void VRAnalyzer::setPathLocalInfo(std::shared_ptr<CodeAnalyzer> SuccAnalyzer,
                                  Instruction* TermInstr,
                                  unsigned SuccIdx) {
  // TODO extract more specific ranges from cmp
}

bool VRAnalyzer::requiresInterpretation(Instruction* I) const {
  assert(I);
  if (CallBase* CB = dyn_cast<CallBase>(I)) {
    if (!CB->isIndirectCall()) {
      Function* Called = CB->getCalledFunction();
      return Called
          && !(Called->isIntrinsic() || isMathCallInstruction(Called->getName().str()) || isMallocLike(Called)
               || Called->empty() // function prototypes
          );
    }
    return true;
  }
  // I is not a call.
  return false;
}

void VRAnalyzer::prepareForCall(Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, VRAFunctionInfo& VFI, bool& isRangeChanged) {
  CallBase* CB = cast<CallBase>(I);
  assert(!CB->isIndirectCall());

  LLVM_DEBUG(Logger->logInstruction(I));
  LLVM_DEBUG(Logger->logInfoln("preparing for function interpretation..."));

  LLVM_DEBUG(
    Logger->lineHead();
    log() << "Loading argument ranges: ");
  // fetch ranges of arguments
  std::list<std::shared_ptr<ValueInfo>> ArgRanges;
  for (Value* Arg : CB->args()) {
    auto node = getNode(Arg);
    ArgRanges.push_back(node);

    // if (VFI.lastRangeArgs.count(Arg)) {
    //   auto IncomingRange = getRange(node);
    //   if (isNewRangeWiden(VFI.lastRangeArgs[Arg], IncomingRange)) {
    //     isRangeChanged = true;
    //     VFI.lastRangeArgs[Arg] = IncomingRange;
    //   }
    // } else {
    //   VFI.lastRangeArgs.try_emplace(Arg, getRange(getNode(Arg)));
    //   isRangeChanged = true;
    // }
    LLVM_DEBUG(log() << VRALogger::toString(fetchRangeNode(Arg)) << ", ");
  }
  LLVM_DEBUG(log() << "\n");

  std::shared_ptr<VRAFunctionStore> FStore = std::static_ptr_cast<VRAFunctionStore>(FunctionStore);
  FStore->setArgumentRanges(*CB->getCalledFunction(), ArgRanges);
}

void VRAnalyzer::returnFromCall(Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, VRAFunctionInfo& VFI, bool& isRangeChanged) {
  CallBase* CB = cast<CallBase>(I);
  assert(!CB->isIndirectCall());

  LLVM_DEBUG(
    Logger->logInstruction(I);
    Logger->logInfo("returning from call"));

  // std::shared_ptr<VRAFunctionStore> FStore = std::static_ptr_cast<VRAFunctionStore>(FunctionStore);
  // std::shared_ptr<ValueInfo> Ret = FStore->getRetVal();
  // if (!Ret) {
  //   LLVM_DEBUG(Logger->logInfoln("function returns nothing"));
  // }
  // else if (std::shared_ptr<ValueInfoWithRange> RetRange = std::dynamic_ptr_cast_or_null<ValueInfoWithRange>(Ret)) {
  //   saveValueRange(I, RetRange);
  //   //VFI.lastRange = getRange(RetRange);
  //   LLVM_DEBUG(logRangeln(I));
  // }
  // else {
  //   setNode(I, Ret);
  //   LLVM_DEBUG(Logger->logRangeln(Ret));
  // }
}

void VRAnalyzer::prepareForCallPropagation(Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, bool& isRangeChanged, VRAFunctionInfo& VFI) {
  CallBase* CB = cast<CallBase>(I);
  assert(!CB->isIndirectCall());

  LLVM_DEBUG(Logger->logInstruction(I));
  LLVM_DEBUG(Logger->logInfoln("preparing for function propagation..."));

  LLVM_DEBUG(
    Logger->lineHead();
    log() << "Loading argument ranges: ");
  // fetch ranges of arguments
  std::list<std::shared_ptr<ValueInfo>> ArgRanges;
  for (Value* Arg : CB->args()) {
    auto node = getNode(Arg);
    ArgRanges.push_back(node);

    if (VFI.lastRangeArgs.count(Arg)) {
      auto IncomingRange = getRange(node);
      if (isNewRangeWiden(VFI.lastRangeArgs[Arg], IncomingRange)) {
        isRangeChanged = true;
        VFI.lastRangeArgs[Arg] = IncomingRange;
        LLVM_DEBUG(tda::log() << " Argomento "<<Arg->getName()<<" allargato ");
      }
    } else {
      isRangeChanged = true;  //new argument
    }
    LLVM_DEBUG(log() << VRALogger::toString(fetchRangeNode(Arg)) << ", ");
  }
  LLVM_DEBUG(log() << "\n");

  if (isRangeChanged) {
    std::shared_ptr<VRAFunctionStore> FStore = std::static_ptr_cast<VRAFunctionStore>(FunctionStore);
    FStore->setArgumentRanges(*CB->getCalledFunction(), ArgRanges);
  }
}

void VRAnalyzer::returnFromCallPropagation(Instruction* I, std::shared_ptr<AnalysisStore> FunctionStore, bool& isRangeChanged, VRAFunctionInfo& VFI) {
  CallBase* CB = cast<CallBase>(I);
  assert(!CB->isIndirectCall());

  LLVM_DEBUG(
    Logger->logInstruction(I);
    Logger->logInfo("returning from call"));

  const std::shared_ptr<Range> oldInfo = fetchRange(I);
  

  std::shared_ptr<VRAFunctionStore> FStore = std::static_ptr_cast<VRAFunctionStore>(FunctionStore);
  std::shared_ptr<ValueInfo> Ret = FStore->getRetVal();
  if (!Ret) {
    LLVM_DEBUG(Logger->logInfoln("function returns nothing"));
  }
  else if (std::shared_ptr<ValueInfoWithRange> RetRange = std::dynamic_ptr_cast_or_null<ValueInfoWithRange>(Ret)) {
    
    const std::shared_ptr<Range> newInfo = getRange(RetRange);
    if (isNewRangeWiden(newInfo, oldInfo)) {
      LLVM_DEBUG(tda::log() << " NARROWING FROM OLD_RANGE = "<< (oldInfo ? oldInfo->toString() : "(none)") << " TO "<< (oldInfo ? newInfo->toString() : "(none)"));
      isRangeChanged = true;
      saveValueRange(I, newInfo);
    } else if (isRangeChanged) {

      saveValueRange(I, RetRange);
      isRangeChanged = isNewRangeWiden(oldInfo, newInfo);
      if (isRangeChanged) {
        LLVM_DEBUG(tda::log() << " (range widen) ");
      }

    } else {
      saveValueRange(I, VFI.lastRange);
      LLVM_DEBUG(tda::log() <<" retreieved past range "<<VFI.lastRange->toString());
    }
    LLVM_DEBUG(logRangeln(I));
  }
  else {
    setNode(I, Ret);
    LLVM_DEBUG(Logger->logRangeln(Ret));
  }
}

std::shared_ptr<Range> VRAnalyzer::getRange(const std::shared_ptr<ValueInfo> VI) {
  if (VI) {
    switch (VI->getKind()) {
    case ValueInfo::K_Scalar: {
      const std::shared_ptr<ScalarInfo> ScalarNode = std::static_ptr_cast<ScalarInfo>(VI);
      return ScalarNode->range;
    }
    case ValueInfo::K_Struct: {
      std::shared_ptr<StructInfo> StructNode = std::static_ptr_cast<StructInfo>(VI);
      std::shared_ptr<Range> summary = nullptr;
      for (const std::shared_ptr<ValueInfo>& Field : *StructNode) {
        const std::shared_ptr<Range> fieldRange = getRange(Field);
        if (!fieldRange)
          continue;
        if (!summary)
          summary = fieldRange->clone();
        else
          *summary = summary->join(*fieldRange);
      }
      return summary;
    }
    case ValueInfo::K_GetElementPointer: {
      return nullptr;
    }
    case ValueInfo::K_Pointer: {
      return nullptr;
    }
    default: llvm_unreachable("Unhandled node type.");
    }
  }
  return nullptr;
}

std::shared_ptr<Range> VRAnalyzer::getBBRange(const llvm::Value *V) {
  return getRange(getNode(V));
}

////////////////////////////////////////////////////////////////////////////////
// Instruction Handlers
////////////////////////////////////////////////////////////////////////////////

void VRAnalyzer::handleSpecialCall(const Instruction* I) {
  const CallBase* CB = cast<CallBase>(I);
  LLVM_DEBUG(Logger->logInstruction(I));

  // fetch function name
  Function* Callee = CB->getCalledFunction();
  if (Callee == nullptr) {
    LLVM_DEBUG(Logger->logInfo("indirect calls not supported"));
    return;
  }

  // check if it's an OMP library function and handle it if so
  if (detectAndHandleLibOMPCall(CB))
    return;

  const StringRef FunctionName = Callee->getName();
  if (isMathCallInstruction(FunctionName.str())) {
    // fetch ranges of arguments
    std::list<std::shared_ptr<Range>> ArgScalarRanges;
    for (Value* Arg : CB->args())
      ArgScalarRanges.push_back(fetchRange(Arg));
    std::shared_ptr<Range> Res = handleMathCallInstruction(ArgScalarRanges, FunctionName.str());
    saveValueRange(I, Res);
    LLVM_DEBUG(Logger->logInfo("whitelisted"));
    LLVM_DEBUG(Logger->logRangeln(Res));
  }
  else if (isMallocLike(Callee)) {
    handleMallocCall(CB);
  }
  else if (Callee->isIntrinsic()) {
    const auto IntrinsicsID = Callee->getIntrinsicID();
    switch (IntrinsicsID) {
    case Intrinsic::memcpy: handleMemCpyIntrinsics(CB); break;
    default: LLVM_DEBUG(Logger->logInfoln("skipping intrinsic " + std::string(FunctionName)));
    }
  }
  else {
    LLVM_DEBUG(Logger->logInfoln("unsupported call"));
  }
}

void VRAnalyzer::handleMemCpyIntrinsics(const Instruction* memcpy) {
  assert(isa<CallInst>(memcpy) || isa<InvokeInst>(memcpy));
  LLVM_DEBUG(Logger->logInfo("llvm.memcpy"));
  const BitCastInst* dest_bitcast = dyn_cast<BitCastInst>(memcpy->getOperand(0U));
  const BitCastInst* src_bitcast = dyn_cast<BitCastInst>(memcpy->getOperand(1U));
  if (!(dest_bitcast && src_bitcast)) {
    LLVM_DEBUG(Logger->logInfo("operand is not bitcast, aborting"));
    return;
  }
  const Value* dest = dest_bitcast->getOperand(0U);
  const Value* src = src_bitcast->getOperand(0U);

  const std::shared_ptr<ValueInfo> src_node = loadNode(getNode(src));
  storeNode(getNode(dest), src_node);
  LLVM_DEBUG(Logger->logRangeln(fetchRangeNode(src)));
}

bool VRAnalyzer::isMallocLike(const Function* F) const {
  const StringRef FName = F->getName();
  // TODO make sure this works in other platforms
  return FName == "malloc" || FName == "calloc" || FName == "_Znwm" || FName == "_Znam";
}

bool VRAnalyzer::isCallocLike(const Function* F) const {
  const StringRef FName = F->getName();
  // TODO make sure this works in other platforms
  return FName == "calloc";
}

void VRAnalyzer::handleMallocCall(const CallBase* CB) {
  LLVM_DEBUG(Logger->logInfo("malloc-like"));
  const Type* AllocatedType = nullptr;

  auto inputInfo = getGlobalStore()->getUserInput(CB);
  if (AllocatedType && AllocatedType->isStructTy()) {
    if (inputInfo && std::isa_ptr<StructInfo>(inputInfo))
      DerivedRanges[CB] = inputInfo->clone();
    else
      DerivedRanges[CB] = std::make_shared<StructInfo>(0);
    LLVM_DEBUG(Logger->logInfoln("struct"));
  }
  else {
    if (!(AllocatedType && AllocatedType->isPointerTy())) {
      if (inputInfo && std::isa_ptr<ScalarInfo>(inputInfo)) {
        DerivedRanges[CB] = std::make_shared<PointerInfo>(inputInfo);
      }
      else if (isCallocLike(CB->getCalledFunction())) {
        DerivedRanges[CB] =
          std::make_shared<PointerInfo>(std::make_shared<ScalarInfo>(nullptr, std::make_shared<Range>(0, 0)));
      }
      else {
        DerivedRanges[CB] = std::make_shared<PointerInfo>(nullptr);
      }
    }
    else {
      DerivedRanges[CB] = std::make_shared<PointerInfo>(nullptr);
    }
    LLVM_DEBUG(Logger->logInfoln("pointer"));
  }
}

bool VRAnalyzer::detectAndHandleLibOMPCall(const CallBase* CB) {
  Function* F = CB->getCalledFunction();
  if (F->getName() == "__kmpc_for_static_init_4") {
    Value* VPLower = CB->getArgOperand(4U);
    Value* VPUpper = CB->getArgOperand(5U);
    std::shared_ptr<Range> PLowerRange = fetchRange(VPLower);
    std::shared_ptr<Range> PUpperRange = fetchRange(VPUpper);
    if (!PLowerRange || !PUpperRange) {
      LLVM_DEBUG(Logger->logInfoln("ranges of plower/pupper unknown, doing nothing"));
      return true;
    }
    std::shared_ptr<Range> Merge = getUnionRange(PLowerRange, PUpperRange);
    saveValueRange(VPLower, Merge);
    saveValueRange(VPUpper, Merge);
    LLVM_DEBUG(Logger->logRange(Merge));
    LLVM_DEBUG(Logger->logInfoln(" set to plower, pupper nodes"));
    return true;
  }
  return false;
}

void VRAnalyzer::handleReturn(const Instruction* ret, bool& isRangeChanged) {
  const ReturnInst* ret_i = cast<ReturnInst>(ret);
  LLVM_DEBUG(Logger->logInstruction(ret));
  if (const Value* ret_val = ret_i->getReturnValue()) {
    std::shared_ptr<ValueInfo> range = getNode(ret_val);

    std::shared_ptr<VRAFunctionStore> FStore;
    if (CodeInt) {
      FStore = std::static_ptr_cast<VRAFunctionStore>(CodeInt->getFunctionStore());
    } else {
      FStore = std::static_ptr_cast<VRAFunctionStore>(ModInt->getFunctionStore());
    }
    FStore->setRetVal(range);

    LLVM_DEBUG(Logger->logRangeln(range));
  }
  else {
    LLVM_DEBUG(Logger->logInfoln("void return."));
  }
}

void VRAnalyzer::handleAllocaInstr(Instruction* I, bool& isRangeChanged) {
  auto* allocaInst = cast<AllocaInst>(I);
  LLVM_DEBUG(Logger->logInstruction(I));
  const auto inputValueInfo = getGlobalStore()->getUserInput(I);
  auto* allocatedType = TaffoInfo::getInstance().getOrCreateTransparentType(*allocaInst);
  const std::shared_ptr<Range> oldInfo = getRange(DerivedRanges[I]);
  LLVM_DEBUG(tda::log() << " ALLOCA OLD_RANGE = "<< (oldInfo ? oldInfo->toString() : "(none)") << " ");
  if (auto* structType = dyn_cast<TransparentStructType>(allocatedType)) {
    if (inputValueInfo && std::isa_ptr<StructInfo>(inputValueInfo))
      DerivedRanges[I] = inputValueInfo->clone();
    else
      DerivedRanges[I] = ValueInfoFactory::create(structType);
    LLVM_DEBUG(Logger->logInfoln("struct"));
  }
  else {
    if (inputValueInfo && std::isa_ptr<ScalarInfo>(inputValueInfo))
      DerivedRanges[I] = std::make_shared<PointerInfo>(inputValueInfo);
    else
      DerivedRanges[I] = std::make_shared<PointerInfo>(nullptr);
    LLVM_DEBUG(Logger->logInfoln("pointer"));
  }
  const std::shared_ptr<Range> newInfo = getRange(DerivedRanges[I]);
  if (newInfo) LLVM_DEBUG(tda::log() << " ALLOCA NEW_RANGE = "<<newInfo->toString() << " ");
  isRangeChanged = isNewRangeWiden(oldInfo, newInfo);
}

void VRAnalyzer::handleStoreInstr(const Instruction* I, bool& isRangeChanged) {
  const StoreInst* Store = cast<StoreInst>(I);
  LLVM_DEBUG(Logger->logInstruction(I));
  const Value* AddressParam = Store->getPointerOperand();
  const Value* ValueParam = Store->getValueOperand();

  if (isa<ConstantPointerNull>(ValueParam))
    return;

  std::shared_ptr<ValueInfo> AddressNode = getNode(AddressParam);
  std::shared_ptr<ValueInfo> ValueNode = getNode(ValueParam);

  const std::shared_ptr<Range> oldValueRange = getRange(ValueNode);
  const std::shared_ptr<Range> oldPointedRange = getRange(loadNode(AddressNode));
  LLVM_DEBUG(tda::log() << " STORE OLD_RANGE = "<< (oldValueRange ? oldValueRange->toString() : "(none)") << " ");

  if (!ValueNode && !ValueParam->getType()->isPointerTy())
    ValueNode = fetchRangeNode(I);

  // Mirror recurrence handling: materialize a scalar node carrying the value
  // range we are about to store so the base pointer receives tightened bounds.
  if (!ValueParam->getType()->isPointerTy()) {
    std::shared_ptr<Range> currentRange = getRange(ValueNode);
    if (!currentRange)
      currentRange = fetchRange(ValueParam);

    if (auto Scalar = std::dynamic_ptr_cast_or_null<ScalarInfo>(ValueNode)) {
      auto Cloned = std::static_pointer_cast<ScalarInfo>(Scalar->clone());
      Cloned->range = currentRange;
      ValueNode = Cloned;
    } else if (!ValueNode) {
      ValueNode = std::make_shared<ScalarInfo>(nullptr, currentRange);
    }
  }

  storeNode(AddressNode, ValueNode);

  const std::shared_ptr<Range> newPointedRange = getRange(loadNode(AddressNode));
  if (newPointedRange) LLVM_DEBUG(tda::log() << " STORE NEW_RANGE = "<<newPointedRange->toString() << " ");
  isRangeChanged = isNewRangeWiden(oldPointedRange, newPointedRange);

  LLVM_DEBUG(Logger->logRangeln(ValueNode));
}

void VRAnalyzer::handleLoadInstr(Instruction* I, bool& isRangeChanged) {
  LoadInst* Load = cast<LoadInst>(I);
  LLVM_DEBUG(Logger->logInstruction(I));
  const Value* PointerOp = Load->getPointerOperand();

  std::shared_ptr<ValueInfo> Loaded = loadNode(getNode(PointerOp));

  const std::shared_ptr<Range> oldInfo = getRange(Loaded);
  LLVM_DEBUG(tda::log() << " LOAD OLD_RANGE = "<< (oldInfo ? oldInfo->toString() : "(none)") << " ");

  if (std::shared_ptr<ScalarInfo> Scalar = std::dynamic_ptr_cast_or_null<ScalarInfo>(Loaded)) {
    llvm::MemorySSAAnalysis::Result *SSARes;
    if (CodeInt) {
      auto& FAM = CodeInt->getMAM().getResult<FunctionAnalysisManagerModuleProxy>(*I->getFunction()->getParent()).getManager();
      SSARes = &(FAM.getResult<MemorySSAAnalysis>(*I->getFunction()));
    } else {
      auto& FAM = ModInt->getMAM().getResult<FunctionAnalysisManagerModuleProxy>(*I->getFunction()->getParent()).getManager();
      SSARes = &(FAM.getResult<MemorySSAAnalysis>(*I->getFunction()));
    }
    
    MemorySSA& memssa = SSARes->getMSSA();
    MemSSAUtils memssa_utils(memssa);
    SmallVectorImpl<Value*>& def_vals = memssa_utils.getDefiningValues(Load);

    Type* load_ty = getFullyUnwrappedType(Load);
    std::shared_ptr<Range> res = Scalar->range;
    for (Value* dval : def_vals)
      if (dval && load_ty->canLosslesslyBitCastTo(getFullyUnwrappedType(dval)))
        res = getUnionRange(res, fetchRange(dval));
    saveValueRange(I, res);

    if (res) LLVM_DEBUG(tda::log() << " LOAD NEW_RANGE = "<<res->toString() << " ");
    isRangeChanged = isNewRangeWiden(oldInfo, res);

    LLVM_DEBUG(Logger->logRangeln(res));
  }
  else if (Loaded) {
    setNode(I, Loaded);
    LLVM_DEBUG(Logger->logInfoln("pointer load"));
  }
  else {
    LLVM_DEBUG(Logger->logInfoln("unable to retrieve loaded value"));
  }
}

void VRAnalyzer::handleGEPInstr(const Instruction* I, bool& isRangeChanged) {
  const GetElementPtrInst* gepInst = cast<GetElementPtrInst>(I);
  LLVM_DEBUG(Logger->logInstruction(gepInst));

  std::shared_ptr<ValueInfo> Node = getNode(gepInst);
  if (Node) {
    LLVM_DEBUG(Logger->logInfoln("has node"));
    return;
  }
  SmallVector<unsigned, 1> Offset;
  if (!extractGEPOffset(
        gepInst->getSourceElementType(), iterator_range(gepInst->idx_begin(), gepInst->idx_end()), Offset)) {
    return;
  }
  Node = std::make_shared<GEPInfo>(getNode(gepInst->getPointerOperand()), Offset);
  setNode(I, Node);
}

void VRAnalyzer::handleBitCastInstr(Instruction* I, bool& isRangeChanged) {
  LLVM_DEBUG(Logger->logInstruction(I));
  if (std::shared_ptr<ValueInfo> Node = getNode(I->getOperand(0U))) {
    bool InputIsStruct = getFullyUnwrappedType(I->getOperand(0U))->isStructTy();
    bool OutputIsStruct = getFullyUnwrappedType(I)->isStructTy();
    if (!InputIsStruct && !OutputIsStruct) {
      setNode(I, Node);
      LLVM_DEBUG(Logger->logRangeln(Node));
    }
    else {
      LLVM_DEBUG(Logger->logInfoln("oh shit -> no node"));
      LLVM_DEBUG(
        log()
        << "This instruction is converting to/from a struct type. Ignoring to avoid generating invalid metadata\n");
    }
  }
  else {
    LLVM_DEBUG(Logger->logInfoln("no node"));
  }
}

void VRAnalyzer::handleCmpInstr(const Instruction* cmp, bool& isRangeChanged) {
  const CmpInst* cmp_i = cast<CmpInst>(cmp);
  LLVM_DEBUG(Logger->logInstruction(cmp));

  const std::shared_ptr<Range> oldInfo = fetchRange(cmp_i);
  
  const CmpInst::Predicate pred = cmp_i->getPredicate();
  std::list<std::shared_ptr<Range>> ranges;
  for (unsigned index = 0; index < cmp_i->getNumOperands(); index++) {
    const Value* op = cmp_i->getOperand(index);
    if (std::shared_ptr<ScalarInfo> op_range = std::dynamic_ptr_cast_or_null<ScalarInfo>(getNode(op)))
      ranges.push_back(op_range->range);
    else
      ranges.push_back(nullptr);
  }
  std::shared_ptr<Range> result = std::dynamic_ptr_cast_or_null<Range>(handleCompare(ranges, pred));
  LLVM_DEBUG(Logger->logRangeln(result));
  saveValueRange(cmp, result);

  LLVM_DEBUG(tda::log() << " CMP OLD_RANGE = "<< (oldInfo ? oldInfo->toString() : "(none)") << " ");
  if (result) LLVM_DEBUG(tda::log() << " CMP NEW_RANGE = "<<result->toString() << " ");
  isRangeChanged = isNewRangeWiden(oldInfo, result);
}

void VRAnalyzer::handlePhiNode(const Instruction* phi, bool& isRangeChanged) {
  const PHINode* phi_n = cast<PHINode>(phi);
  if (phi_n->getNumIncomingValues() == 0U)
    return;
  LLVM_DEBUG(Logger->logInstruction(phi));
  auto res = copyRange(getGlobalStore()->getUserInput(phi));
  
  const std::shared_ptr<Range> oldInfo = fetchRange(phi_n);
  LLVM_DEBUG(tda::log() << " PHI OLD_RANGE = "<< (oldInfo ? oldInfo->toString() : "(none)") << " ");

  for (unsigned index = 0U; index < phi_n->getNumIncomingValues(); index++) {
    const Value* op = phi_n->getIncomingValue(index);
    std::shared_ptr<ValueInfo> op_node = getNode(op);
    if (!op_node)
      continue;
    if (std::shared_ptr<ValueInfoWithRange> op_range = std::dynamic_ptr_cast<ScalarInfo>(op_node)) {
      res = getUnionRange(res, op_range);

      const std::shared_ptr<Range> newInfo = fetchRange(phi_n);
      if (newInfo) LLVM_DEBUG(tda::log() << " PHI NEW_RANGE = "<<newInfo->toString() << " ");
      isRangeChanged = isNewRangeWiden(oldInfo, newInfo);

    }
    else {
      setNode(phi, op_node);
      LLVM_DEBUG(Logger->logInfoln("Pointer PHINode"));
      return;
    }
  }
  setNode(phi, res);

  
  LLVM_DEBUG(Logger->logRangeln(res));
}

void VRAnalyzer::analyzePHIStartInstruction(llvm::Instruction* I, bool& isRangeChanged) {
  const PHINode* phi_n = cast<PHINode>(I);
  if (phi_n->getNumIncomingValues() == 0U)
    return;
  LLVM_DEBUG(Logger->logInstruction(I));

  const Value* op = phi_n->getIncomingValue(0);
  std::shared_ptr<ValueInfo> op_node = getNode(op);
  if (std::shared_ptr<ValueInfoWithRange> op_range = std::dynamic_ptr_cast<ScalarInfo>(op_node)) {
    const std::shared_ptr<ScalarInfo> s_op = std::dynamic_ptr_cast<ScalarInfo>(op_range);
    setNode(I, op_range);
    LLVM_DEBUG(Logger->logRangeln(op_range));
  } else {
    LLVM_DEBUG(tda::log() << "unable to retreve start operand of phi node\n");
  }
}

void VRAnalyzer::handleSelect(const Instruction* i, bool& isRangeChanged) {
  const SelectInst* sel = cast<SelectInst>(i);
  // TODO handle pointer select
  LLVM_DEBUG(Logger->logInstruction(sel));
  std::shared_ptr<ValueInfoWithRange> res =
    getUnionRange(fetchRangeNode(sel->getFalseValue()), fetchRangeNode(sel->getTrueValue()));
  LLVM_DEBUG(Logger->logRangeln(res));
  saveValueRange(i, res);
}

////////////////////////////////////////////////////////////////////////////////
// Data Handling
////////////////////////////////////////////////////////////////////////////////

std::shared_ptr<Range> VRAnalyzer::fetchRange(const Value* v) {
  if (const std::shared_ptr<Range> Derived = VRAStore::fetchRange(v))
    return Derived;

  if (const std::shared_ptr<ValueInfoWithRange> InputRange = getGlobalStore()->getUserInput(v))
    if (const std::shared_ptr<ScalarInfo> InputScalar = std::dynamic_ptr_cast<ScalarInfo>(InputRange))
      return InputScalar->range;

  return nullptr;
}

std::shared_ptr<ValueInfoWithRange> VRAnalyzer::fetchRangeNode(const Value* v) {
  if (const std::shared_ptr<ValueInfoWithRange> Derived = VRAStore::fetchRangeNode(v)) {
    if (std::isa_ptr<StructInfo>(Derived)) {
      if (auto InputRange = getGlobalStore()->getUserInput(v)) {
        // fill null input_range fields with corresponding derived fields
        return fillRangeHoles(Derived, InputRange->clone<ValueInfoWithRange>());
      }
    }
    return Derived;
  }

  if (const auto InputRange = getGlobalStore()->getUserInput(v))
    return InputRange->clone<ValueInfoWithRange>();

  return nullptr;
}

std::shared_ptr<ValueInfo> VRAnalyzer::getNode(const Value* v) {
  std::shared_ptr<ValueInfo> Node = VRAStore::getNode(v);

  if (!Node) {
    std::shared_ptr<VRAStore> ExternalStore = getAnalysisStoreForValue(v);
    if (ExternalStore)
      Node = ExternalStore->getNode(v);
  }

  if (Node && Node->getKind() == ValueInfo::K_Scalar) {
    auto UserInput = std::dynamic_ptr_cast_or_null<ScalarInfo>(getGlobalStore()->getUserInput(v));
    if (UserInput && UserInput->isFinal())
      Node = UserInput->clone();
  }

  return Node;
}

void VRAnalyzer::setNode(const Value* V, std::shared_ptr<ValueInfo> Node) {
  if (isa<GlobalVariable>(V)) {
    // set node in global analyzer
    getGlobalStore()->setNode(V, Node);
    return;
  }
  if (isa<Argument>(V)) {
    std::shared_ptr<VRAFunctionStore> FStore;
    if (CodeInt) FStore = std::static_ptr_cast<VRAFunctionStore>(CodeInt->getFunctionStore());
    else FStore = std::static_ptr_cast<VRAFunctionStore>(ModInt->getFunctionStore());
    FStore->setNode(V, Node);
    return;
  }

  VRAStore::setNode(V, Node);
}

void VRAnalyzer::logRangeln(const Value* v) {
  LLVM_DEBUG(
    if (getGlobalStore()->getUserInput(v))
      log() << "(possibly from metadata) ");
  LLVM_DEBUG(Logger->logRangeln(fetchRangeNode(v)));
}

void VRAnalyzer::fallbackCMP(const Instruction* I) {
  saveValueRange(I, getGenericBoolRange());
  LLVM_DEBUG({
    Logger->logInstruction(I);
    Logger->logInfoln("fallback CMP range forced to [0,1]");
  });
}

size_t VRAnalyzer::compareLoadStoreDim(VRAFunctionInfo VFI, const llvm::Value *load, const llvm::Value *store) {

  const auto *LoadI = dyn_cast<LoadInst>(load);
  const auto *StoreI = dyn_cast<StoreInst>(store);
  if (!LoadI || !StoreI)
    return 0;
    
  auto getRootPtr = [&](Instruction *I) -> const Value * {
    const Value *Ptr = isa<LoadInst>(I) ? cast<LoadInst>(I)->getPointerOperand()
                                        : cast<StoreInst>(I)->getPointerOperand();
    if (!Ptr)
      return nullptr;

    if (auto *PtrV = const_cast<Value *>(Ptr))
      if (Value *Origin = MemSSAUtils::getOriginPointer(*VFI.MSSA, PtrV))
        return Origin;
    return Ptr;
  };
  
  const Value *LoadPtr = getRootPtr(const_cast<LoadInst*>(LoadI));
  const Value *StorePtr = getRootPtr(const_cast<StoreInst*>(StoreI));
  if (!LoadPtr || !StorePtr)
    return 0;
    
  const int LoadDim = getArrayAccessDimFromPtr(LoadPtr);
  const int StoreDim = getArrayAccessDimFromPtr(StorePtr);
  if (LoadDim < 0 || StoreDim < 0 || LoadDim <= StoreDim)
    return 0;

  return static_cast<size_t>(LoadDim - StoreDim);

}

void VRAnalyzer::resolveRecurrence(VRARecurrenceInfo& VRI, unsigned TripCount, bool& isRangeChanged) {
  if (!VRI.RR || TripCount == 0) return;

  LLVM_DEBUG(Logger->logInstruction(VRI.root));

  // already solved, solve again just for higher trip count
  if (VRI.lastRange && VRI.lastRangeComputedAt >= TripCount) {
    LLVM_DEBUG(tda::log() << " RR already solved.\n");
    return;
  }

  if (TripCount > 0) {

    auto rangeAtZero = VRI.RR->at(0);
    auto rangeAtTC = VRI.RR->at(TripCount);

    std::shared_ptr<taffo::Range> joinedRange;
    if (!rangeAtZero || rangeAtZero == Range::Top().clone()) {
      joinedRange = rangeAtTC;
    } else {
      joinedRange = std::make_shared<Range>(rangeAtZero->join(*rangeAtTC));
    }
    
    VRI.lastRange = joinedRange;
    VRI.lastRangeComputedAt = TripCount;
    LLVM_DEBUG(tda::log() << " resolved RR " << *VRI.root << ".at("<<TripCount<<") ");
    isRangeChanged = true; // with new solved RR is always changed = true

    if (auto* PN = dyn_cast<PHINode>(VRI.root)) {

      const Value* op = PN->getIncomingValue(0);
      std::shared_ptr<ValueInfo> op_node = getNode(op);
      if (std::shared_ptr<ValueInfoWithRange> op_range = std::dynamic_ptr_cast<ScalarInfo>(op_node)) {
        const std::shared_ptr<ScalarInfo> s_op = std::dynamic_ptr_cast<ScalarInfo>(op_range);
        s_op->range = joinedRange;
        setNode(VRI.root, s_op);
        LLVM_DEBUG(Logger->logRangeln(op_range));
      }
      return;
    } else if (auto Store = dyn_cast<StoreInst>(VRI.root)) {
      
      const Value* AddressParam = Store->getPointerOperand();
      const Value* ValueParam = Store->getValueOperand();

      if (isa<ConstantPointerNull>(ValueParam)) return;

      std::shared_ptr<ValueInfo> AddressNode = getNode(AddressParam);
      std::shared_ptr<ValueInfo> ValueNode = getNode(ValueParam);

      if (!ValueNode && !ValueParam->getType()->isPointerTy())
        ValueNode = fetchRangeNode(VRI.root);
        
      if (!ValueParam->getType()->isPointerTy()) {
        if (auto Scalar = std::dynamic_ptr_cast_or_null<ScalarInfo>(ValueNode)) {
          auto Cloned = std::static_pointer_cast<ScalarInfo>(Scalar->clone());
          Cloned->range = joinedRange;
          ValueNode = Cloned;
        } else if (!ValueNode) {
          ValueNode = std::make_shared<ScalarInfo>(nullptr, joinedRange);
        }
      }

      storeNode(AddressNode, ValueNode);
      LLVM_DEBUG(Logger->logRangeln(joinedRange));
      return;
    }
  }
  LLVM_DEBUG(tda::log() << "unable to resolve and store recurrence\n");
}

void VRAnalyzer::retrieveSolvedRecurrence(llvm::Instruction* I, VRARecurrenceInfo& VRI, bool& isRangeChanged) {
  if (!VRI.lastRange) return;

  LLVM_DEBUG(Logger->logInstruction(I));

  if (auto* PN = dyn_cast<PHINode>(VRI.root)) {

      auto oldNode = getNode(I);
      if (!oldNode) isRangeChanged = true;

      const Value* op = PN->getIncomingValue(0);
      std::shared_ptr<ValueInfo> op_node = getNode(op);
      if (std::shared_ptr<ValueInfoWithRange> op_range = std::dynamic_ptr_cast<ScalarInfo>(op_node)) {
        const std::shared_ptr<ScalarInfo> s_op = std::dynamic_ptr_cast<ScalarInfo>(op_range);
        s_op->range = VRI.lastRange;
        setNode(VRI.root, s_op);
        LLVM_DEBUG(Logger->logRangeln(op_range));
        if (oldNode && isNewRangeWiden(getRange(oldNode), VRI.lastRange)) isRangeChanged = true;
      }
      return;
    } else if (auto Store = dyn_cast<StoreInst>(VRI.root)) {

      const Value* AddressParam = Store->getPointerOperand();
      const Value* ValueParam = Store->getValueOperand();

      if (isa<ConstantPointerNull>(ValueParam)) return;

      std::shared_ptr<ValueInfo> AddressNode = getNode(AddressParam);
      std::shared_ptr<ValueInfo> ValueNode = getNode(ValueParam);

      if (!ValueNode && !ValueParam->getType()->isPointerTy())
        ValueNode = fetchRangeNode(VRI.root);
        
      if (!ValueParam->getType()->isPointerTy()) {
        if (auto Scalar = std::dynamic_ptr_cast_or_null<ScalarInfo>(ValueNode)) {
          auto Cloned = std::static_pointer_cast<ScalarInfo>(Scalar->clone());
          Cloned->range = VRI.lastRange;
          ValueNode = Cloned;
        } else if (!ValueNode) {
          ValueNode = std::make_shared<ScalarInfo>(nullptr, VRI.lastRange);
        }
      }

      storeNode(AddressNode, ValueNode);
      LLVM_DEBUG(Logger->logRangeln(VRI.lastRange));
      return;
    }

}

std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildAffinePHIRecurrence(const llvm::PHINode *phi) {

  const Value* op = phi->getIncomingValue(0);
  std::shared_ptr<ValueInfo> op_node = getNode(op);
  std::shared_ptr<Range> StartRange = getRange(op_node);

  const Value* op_1 = phi->getIncomingValue(1);
  std::shared_ptr<ValueInfo> op_node_1 = getNode(op_1);
  std::shared_ptr<Range> StepRange = getRange(op_node_1);

  StepRange = handleSub(StepRange, StartRange);

  return std::make_shared<AffineRangedRecurrence>(std::move(StartRange), std::move(StepRange));
}

std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildAffineFlattingRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* Store) {

  auto StartRange = getRange(getNode(VRI.loadJunction));

  auto StepRange = getRange(getNode(VRI.loadHigherDim));
  StepRange = handleSub(StepRange, StartRange);

  return std::make_shared<AffineRangedRecurrence>(std::move(StartRange), std::move(StepRange));
}

// valid when delta index is 1
std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildAffineStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* Store) {

  auto StartRange = getRange(getNode(VRI.loadJunction));
  if (!StartRange) StartRange = Range::Top().clone();

  auto op = Store->getValueOperand();
  auto StepRange = getRange(getNode(op));
  
  StepRange = handleSub(StepRange, StartRange);
  return std::make_shared<AffineRangedRecurrence>(std::move(StartRange), std::move(StepRange));
}

std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildFakeStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* Store) {

  auto StartRange = getRange(getNode(VRI.loadJunction));
  if (!StartRange) StartRange = Range::Top().clone();

  auto op = Store->getValueOperand();
  auto StepRange = getRange(getNode(op));

  StepRange = StartRange->join(StepRange);

  return std::make_shared<FakeRangedRecurrence>(std::move(StartRange), std::move(StepRange));
}

std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildInitRecurrence(std::shared_ptr<Range> LastStoredRange, const llvm::StoreInst* Store) {

  auto op = Store->getValueOperand();
  auto StartRange = getRange(getNode(op));

  if (LastStoredRange)
    StartRange = LastStoredRange->join(StartRange);
  
  return std::make_shared<InitRangedRecurrence>(std::move(StartRange));
}

std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildGeometricPHIRecurrence(const llvm::PHINode *phi) {

  const Value* op = phi->getIncomingValue(0);
  std::shared_ptr<ValueInfo> op_node = getNode(op);
  std::shared_ptr<Range> StartRange = getRange(op_node);

  const Value* op_1 = phi->getIncomingValue(1);
  std::shared_ptr<ValueInfo> op_node_1 = getNode(op_1);
  std::shared_ptr<Range> StepRatio = getRange(op_node_1);
  
  StepRatio = handleDiv(StepRatio, StartRange);

  LLVM_DEBUG(tda::log() << "recognized geometric(start= " << (StartRange ? StartRange->toString() : "(none)") << ", ratio= " << StepRatio->toString() << ")\n\n");
  return std::make_shared<GeometricRangedRecurrence>(std::move(StartRange), std::move(StepRatio));
}

std::shared_ptr<taffo::RangedRecurrence> VRAnalyzer::buildGeometricStoreRecurrence(VRARecurrenceInfo VRI, const llvm::StoreInst* Store) {

  auto StartRange = getRange(getNode(VRI.loadJunction));

  auto op = Store->getValueOperand();
  auto StepRatio = getRange(getNode(op));
  
  StepRatio = handleDiv(StepRatio, StartRange);

  LLVM_DEBUG(tda::log() << "recognized geometric(start= " << (StartRange ? StartRange->toString() : "(none)") << ", ratio= " << StepRatio->toString() << ")\n\n");
  return std::make_shared<GeometricRangedRecurrence>(std::move(StartRange), std::move(StepRatio));
}

std::shared_ptr<RangedRecurrence> VRAnalyzer::buildUnknownRecurrence(const llvm::Value *V) {

  auto StartRange = getRange(getNode(V));
  auto StepRange = Range::Top().clone();

  LLVM_DEBUG(tda::log() << "recognized unknown(start= " << (StartRange ? StartRange->toString() : "(none)") << ", step= " << StepRange->toString() << ")\n\n");
  return std::make_shared<AffineRangedRecurrence>(std::move(StartRange), std::move(StepRange));
}
