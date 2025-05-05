#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"

using namespace llvm;

namespace {

// Primo Pass: Algebraic Identity
struct AlgebraicIdentityPass : public PassInfoMixin<AlgebraicIdentityPass> {
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
        for (auto &BB : F) {
            for (auto it = BB.begin(), end = BB.end(); it != end;) {
                Instruction *I = &*it++;
                if (auto *binOp = dyn_cast<BinaryOperator>(I)) {
                    if (binOp->getOpcode() == Instruction::Add) {
                        if (auto *C = dyn_cast<ConstantInt>(binOp->getOperand(1))) {
                            if (C->isZero()) {
                                binOp->replaceAllUsesWith(binOp->getOperand(0));
                                binOp->eraseFromParent();
                                continue;
                            }
                        }
                        if (auto *C = dyn_cast<ConstantInt>(binOp->getOperand(0))) {
                            if (C->isZero()) {
                                binOp->replaceAllUsesWith(binOp->getOperand(1));
                                binOp->eraseFromParent();
                                continue;
                            }
                        }
                    }
                    if (binOp->getOpcode() == Instruction::Mul) {
                        if (auto *C = dyn_cast<ConstantInt>(binOp->getOperand(1))) {
                            if (C->isOne()) {
                                binOp->replaceAllUsesWith(binOp->getOperand(0));
                                binOp->eraseFromParent();
                                continue;
                            }
                        }
                        if (auto *C = dyn_cast<ConstantInt>(binOp->getOperand(0))) {
                            if (C->isOne()) {
                                binOp->replaceAllUsesWith(binOp->getOperand(1));
                                binOp->eraseFromParent();
                                continue;
                            }
                        }
                    }
                }
            }
        }
        return PreservedAnalyses::none();
    }
};

// Secondo Pass: Strength Reduction
struct StrengthReductionPass : public PassInfoMixin<StrengthReductionPass> {
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
        for (auto &BB : F) {
            for (auto it = BB.begin(), end = BB.end(); it != end;) {
                Instruction *I = &*it++;
                if (auto *binOp = dyn_cast<BinaryOperator>(I)) {
                    if (binOp->getOpcode() == Instruction::Mul) {
                        Value *op0 = binOp->getOperand(0);
                        Value *op1 = binOp->getOperand(1);
                        if (auto *C = dyn_cast<ConstantInt>(op0)) {
                            if (C->equalsInt(15)) std::swap(op0, op1);
                        }
                        if (auto *C = dyn_cast<ConstantInt>(op1)) {
                            if (C->equalsInt(15)) {
                                auto *shiftInst = BinaryOperator::CreateShl(op0, ConstantInt::get(op0->getType(), 4), "shift", binOp);
                                auto *newInst = BinaryOperator::CreateSub(shiftInst, op0, "sub", binOp);
                                binOp->replaceAllUsesWith(newInst);
                                binOp->eraseFromParent();
                                continue;
                            }
                        }
                    }
                    if (binOp->getOpcode() == Instruction::SDiv) {
                        Value *op0 = binOp->getOperand(0);
                        Value *op1 = binOp->getOperand(1);
                        if (auto *C = dyn_cast<ConstantInt>(op1)) {
                            if (C->equalsInt(8)) {
                                auto *shiftInst = BinaryOperator::CreateAShr(op0, ConstantInt::get(op0->getType(), 3), "ashr", binOp);
                                binOp->replaceAllUsesWith(shiftInst);
                                binOp->eraseFromParent();
                                continue;
                            }
                        }
                    }
                }
            }
        }
        return PreservedAnalyses::none();
    }
};

// Terzo Pass: Multi-Instruction Optimization (ora supporta store/load)
struct MultiInstructionOptimizationPass : public PassInfoMixin<MultiInstructionOptimizationPass> {
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
        for (auto &BB : F) {
            for (auto it = BB.begin(), end = BB.end(); it != end;) {
                Instruction *I = &*it++;

                // Trova l'istruzione di add (b + 1)
                if (auto *addInst = dyn_cast<BinaryOperator>(I)) {
                    if (addInst->getOpcode() == Instruction::Add) {
                        Value *b = nullptr;
                        if (auto *C = dyn_cast<ConstantInt>(addInst->getOperand(1))) {
                            if (C->equalsInt(1)) b = addInst->getOperand(0);
                        } else if (auto *C = dyn_cast<ConstantInt>(addInst->getOperand(0))) {
                            if (C->equalsInt(1)) b = addInst->getOperand(1);
                        }
                        if (!b) continue;

                        // Trova il successivo store di addInst
                        if (it != end) {
                            if (auto *store1 = dyn_cast<StoreInst>(&*it)) {
                                if (store1->getValueOperand() == addInst) {
                                    Value *allocaPtr = store1->getPointerOperand();

                                    auto nextIt = std::next(it);
                                    if (nextIt != end) {
                                        if (auto *load = dyn_cast<LoadInst>(&*nextIt)) {
                                            if (load->getPointerOperand() == allocaPtr) {
                                                auto nextNextIt = std::next(nextIt);
                                                if (nextNextIt != end) {
                                                    if (auto *subInst = dyn_cast<BinaryOperator>(&*nextNextIt)) {
                                                        if (subInst->getOpcode() == Instruction::Sub) {
                                                            if (subInst->getOperand(0) == load) {
                                                                if (auto *C2 = dyn_cast<ConstantInt>(subInst->getOperand(1))) {
                                                                    if (C2->equalsInt(1)) {
                                                                        subInst->setOperand(0, b);
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return PreservedAnalyses::none();
    }
};

} // end anonymous namespace

// Parte per registrare i pass nel plugin
extern "C" ::llvm::PassPluginLibraryInfo llvmGetPassPluginInfo() {
    return {LLVM_PLUGIN_API_VERSION, "TestPass", LLVM_VERSION_STRING,
            [](PassBuilder &PB) {
                PB.registerPipelineParsingCallback(
                    [](StringRef Name, FunctionPassManager &FPM,
                       ArrayRef<PassBuilder::PipelineElement>) {
                        if (Name == "algebraic-identity") {
                            FPM.addPass(AlgebraicIdentityPass());
                            return true;
                        }
                        if (Name == "strength-reduction") {
                            FPM.addPass(StrengthReductionPass());
                            return true;
                        }
                        if (Name == "multi-instruction") {
                            FPM.addPass(MultiInstructionOptimizationPass());
                            return true;
                        }
                        return false;
                    });
            }};
}