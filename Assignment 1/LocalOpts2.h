#ifndef LLVM_TRANSFORMS_LOCALOPTS2_H
#define LLVM_TRANSFORMS_LOCALOPTS2_H

#include "llvm/IR/PassManager.h"
#include "llvm/IR/Constants.h"

namespace llvm {
    class LocalOpts2 : public PassInfoMixin<LocalOpts2> {
    public:
        PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };
} // namespace llvm
#endif