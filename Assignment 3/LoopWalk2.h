#ifndef LLVM_TRANSFORMS_LOOPWALK2_H
#define LLVM_TRANSFORMS_LOOPWALK2_H

#include "llvm/IR/PassManager.h"
#include <llvm/Transforms/Scalar/LoopPassManager.h>

namespace llvm {
	class LoopWalk2 : public PassInfoMixin<LoopWalk2> {
	public:
		PreservedAnalyses run(Loop &L, LoopAnalysisManager &LAM, LoopStandardAnalysisResults &LAR, LPMUpdater &LU);
	};
}
#endif //LLVM_TRANSFORMS_LOOPPASS_H