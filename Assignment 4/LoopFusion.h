#ifndef LLVM_TRANSFORMS_LOOPFUSION_H
#define LLVM_TRANSFORMS_LOOPFUSION_H
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"

namespace llvm {
    class LoopFusion : public  PassInfoMixin<LoopFusion> {
          public : PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
    };
}
#endif

