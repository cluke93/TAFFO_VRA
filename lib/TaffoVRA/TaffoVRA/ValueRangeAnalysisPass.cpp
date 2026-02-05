#include "Debug/Logger.hpp"
#include "TaffoInfo/TaffoInfo.hpp"
#include "VRAGlobalStore.hpp"
#include "ValueRangeAnalysisPass.hpp"
#include "ModuleInterpreter.hpp"

#include <llvm/Analysis/MemorySSA.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Support/raw_ostream.h>

#define DEBUG_TYPE "taffo-vra"

using namespace llvm;
using namespace tda;
using namespace taffo;

namespace taffo {

cl::opt<bool> PropagateAll("propagate-all",
                          cl::desc("Propagate ranges for all functions, not only those marked as starting point."),
                          cl::init(false));

cl::opt<unsigned> Unroll("unroll",
                          cl::desc("Default loop unroll count. Setting this to 0 disables loop unrolling. (Default: 1)"),
                          cl::value_desc("count"),
                          cl::init(1U));

cl::opt<unsigned> MaxUnroll("max-unroll",
                          cl::desc("Max loop unroll count. Setting this to 0 disables loop unrolling. (Default: 256)"),
                          cl::value_desc("count"),
                          cl::init(256U));

cl::opt<bool> UseOldVRA("use-old-vra",
                          cl::desc("Flag this to analyze by using old VRA. (Default: false)"),
                          cl::init(false));

cl::opt<bool> ShowRangeCompareTable("show-range-compare-table",
                          cl::desc("Show comparison table between old and new VRA (Default: true)"),
                          cl::init(false));

cl::opt<unsigned> MaxPropagation("max-propagation",
                          cl::desc("Max propagation iterations before stopping (10 is the default, 0 disables the limit)."),
                          cl::init(10U));

} // namespace taffo

PreservedAnalyses ValueRangeAnalysisPass::run(Module& M, ModuleAnalysisManager& AM) {
  LLVM_DEBUG(log().logln("[ValueRangeAnalysisPass]", Logger::Magenta));

  // No need to initialize if memToReg is run before in the same opt call
  // TaffoInfo::getInstance().initializeFromFile("taffo_info_memToReg.json", M);

  std::shared_ptr<VRAGlobalStore> GlobalStore = std::make_shared<VRAGlobalStore>();
  GlobalStore->harvestValueInfo(M);

  if (UseOldVRA) {
    CodeInterpreter CodeInt(AM, GlobalStore, Unroll, MaxUnroll);
    processModule(CodeInt, M);
  } else {
    ModuleInterpreter ModInt(M, AM, GlobalStore);
    ModInt.interpret();
    ModInt.printRecurrenceSummary(llvm::errs());
  }

  LLVM_DEBUG(log() << "saving results...\n");
  GlobalStore->saveResults(M);

  TaffoInfo::getInstance().dumpToFile(VRA_TAFFO_INFO, M);
  LLVM_DEBUG(log().logln("[End of ValueRangeAnalysisPass]", Logger::Magenta));
  return PreservedAnalyses::all();
}

void ValueRangeAnalysisPass::processModule(CodeInterpreter& CodeInt, Module& M) {
  bool FoundVisitableFunction = false;
  for (Function& F : M) {
    if (!F.empty() && (PropagateAll || TaffoInfo::getInstance().isStartingPoint(F))) {
      CodeInt.interpretFunction(&F);
      FoundVisitableFunction = true;
    }
  }

  if (!FoundVisitableFunction)
    LLVM_DEBUG(log() << " No visitable functions found.\n");
}
