//=============================================================================
// FILE: MyPasses.cpp
//
// Implementazione di tre pass LLVM:
//   1) Algebraic Identity Pass
//   2) Strength Reduction Pass
//   3) Multi-Instruction Optimization Pass
//
// Per compilarli come plugin:
//
//   1. Scrivere un CMakeLists.txt che trova LLVM e genera la .so (o .dylib).
//   2. Lanciare 'opt' con:
//        opt -load-pass-plugin=./libMyPasses.so \
//            -passes="algebraic-id-pass" -disable-output input.ll
//      (e analogamente "strength-reduction-pass", "multi-instr-pass", ecc.)
//
//=============================================================================
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace llvm::PatternMatch; // Per usare il matching combinator di LLVM

// ---------------------------------------------------------------------------
// 1. Algebraic Identity Pass
// ---------------------------------------------------------------------------
namespace {
struct AlgebraicIdentityPass : public PassInfoMixin<AlgebraicIdentityPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    bool changed = false;

    // Iteriamo su tutte le istruzioni della funzione
    for (auto &BB : F) {
      for (auto &I : BB) {
        // Pattern #1: (x + 0) => x
        // Pattern #2: (x * 1) => x
        // Useremo il "PatternMatch" (match() e match combinators)
        // Esempi:
        //   m_Add(m_Value(X), m_ConstantInt(C)) ...
        //   m_Mul(m_Value(X), m_ConstantInt(C)) ...
        // Oppure possiamo fare dynamic_cast su BinaryOperator e controllare i valori.

        if (auto *BinOp = dyn_cast<BinaryOperator>(&I)) {
          switch (BinOp->getOpcode()) {
          case Instruction::Add:
          {
            // Cerchiamo: x + 0 => x
            Value *X, *Y;
            // Pattern: Add(X, 0)
            if (match(BinOp, m_Add(m_Value(X), m_ConstantInt<0>(&Y)))) {
              BinOp->replaceAllUsesWith(X);
              BinOp->eraseFromParent();
              changed = true;
              // Attenzione: dopo eraseFromParent(), la variabile BinOp non è più valida,
              // quindi dobbiamo interrompere il loop interno. Un modo semplice è usare un goto
              // o ricominciare la scansione. Qui, per semplicità, facciamo un "break".
              break;
            }
          }
          break;

          case Instruction::Mul:
          {
            // Cerchiamo: x * 1 => x
            Value *X, *Y;
            // Pattern: Mul(X, 1)
            if (match(BinOp, m_Mul(m_Value(X), m_ConstantInt<1>(&Y)))) {
              BinOp->replaceAllUsesWith(X);
              BinOp->eraseFromParent();
              changed = true;
              break;
            }
          }
          break;

          default:
            // Altri opcode non ci interessano in questo pass
            break;
          } // switch
        } // if (BinaryOperator)
      } // for (I)
    } // for (BB)

    // Se abbiamo cambiato l’IR, le analisi esistenti potrebbero essere invalidate
    // In questo pass semplice diciamo di invalidarle tutte
    if (changed) {
      return PreservedAnalyses::none();
    }
    return PreservedAnalyses::all();
  }

  // Questo pass deve essere eseguito anche se la funzione ha l’attributo "optnone".
  static bool isRequired() { return true; }
};
} // anonymous namespace

// ---------------------------------------------------------------------------
// 2. Strength Reduction Pass
// ---------------------------------------------------------------------------
namespace {
struct StrengthReductionPass : public PassInfoMixin<StrengthReductionPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    bool changed = false;
    LLVMContext &Ctx = F.getContext();

    for (auto &BB : F) {
      // Attenzione: quando eliminiamo un’istruzione dentro un for range su BB,
      // potremmo invalidare l’iteratore. Per semplicità useremo un approccio
      // di "collezionare" le istruzioni da modificare ed eseguirle alla fine.
      // Oppure iteriamo in modo "classico" con iteratore e post-increment.
      for (auto InstIt = BB.begin(); InstIt != BB.end();) {
        Instruction &I = *InstIt++;

        if (auto *BinOp = dyn_cast<BinaryOperator>(&I)) {
          // Cerchiamo i pattern:
          //   a) (x * 15) => (x << 4) - x
          //   b) (x / 8)  => x >> 3
          //      (attenzione a sign/unsign, qui assumiamo sdiv di interi non negativi)
          switch (BinOp->getOpcode()) {
          case Instruction::Mul:
          {
            Value *X;
            ConstantInt *C;
            // Pattern: Mul(X, 15)
            if (match(BinOp, m_Mul(m_Value(X), m_ConstantInt(C)))) {
              if (C->equalsInt(15)) {
                // Costruiamo (x << 4) - x
                IRBuilder<> Builder(BinOp);
                // x << 4
                Value *Shifted = Builder.CreateShl(X, ConstantInt::get(X->getType(), 4));
                // (x << 4) - x
                Value *NewVal = Builder.CreateSub(Shifted, X);
                BinOp->replaceAllUsesWith(NewVal);
                BinOp->eraseFromParent();
                changed = true;
              }
            }
          }
          break;

          case Instruction::SDiv:
          case Instruction::UDiv:
          {
            Value *X;
            ConstantInt *C;
            // Cerchiamo x / 8 => x >> 3
            if (match(BinOp, m_UDiv(m_Value(X), m_ConstantInt(C))) || 
                match(BinOp, m_SDiv(m_Value(X), m_ConstantInt(C)))) {
              if (C->equalsInt(8)) {
                IRBuilder<> Builder(BinOp);
                // Creiamo lo shift a destra di 3
                Value *Shifted = Builder.CreateLShr(X, ConstantInt::get(X->getType(), 3));
                // Sostituiamo
                BinOp->replaceAllUsesWith(Shifted);
                BinOp->eraseFromParent();
                changed = true;
              }
            }
          }
          break;

          default:
            // Non gestiamo altri opcode in questo pass
            break;
          }
        }
      }
    }

    if (changed) {
      return PreservedAnalyses::none();
    }
    return PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};
} // anonymous namespace

// ---------------------------------------------------------------------------
// 3. Multi-Instruction Optimization Pass
// ---------------------------------------------------------------------------
namespace {
struct MultiInstructionOptPass : public PassInfoMixin<MultiInstructionOptPass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
    bool changed = false;

    // Vogliamo riconoscere la sequenza:
    //   a = b + 1
    //   c = a - 1
    // trasformandola in:
    //   a = b + 1
    //   c = b
    //
    // In IR (semplificando) potremmo avere:
    //
    //   %a = add i32 %b, 1
    //   %c = sub i32 %a, 1
    //
    // Verifichiamo se la costante 1 coincide, e poi sostituiamo %c con %b

    for (auto &BB : F) {
      // Usiamo un iteratore classico per poter manipolare la lista di istruzioni
      for (auto InstIt = BB.begin(); InstIt != BB.end(); ) {
        Instruction *I = &(*InstIt++);
        // Cerchiamo "sub i32 %a, 1"
        if (auto *SubOp = dyn_cast<BinaryOperator>(I)) {
          if (SubOp->getOpcode() == Instruction::Sub) {
            // sub (a, 1)?
            Value *A;
            ConstantInt *C1;
            if (match(SubOp, m_Sub(m_Value(A), m_ConstantInt(C1))) && C1->equalsInt(1)) {
              // Controlliamo se 'A' è (b + 1).
              // A potrebbe essere un "add i32 b, 1"
              if (auto *AddOp = dyn_cast<BinaryOperator>(A)) {
                if (AddOp->getOpcode() == Instruction::Add) {
                  Value *B;
                  ConstantInt *C2;
                  if (match(AddOp, m_Add(m_Value(B), m_ConstantInt(C2))) && C2->equalsInt(1)) {
                    // ABBIAMO TROVATO IL PATTERN:
                    //   A = B + 1
                    //   C = A - 1  => C = B
                    //
                    // Quindi SubOp => C = B
                    SubOp->replaceAllUsesWith(B);
                    SubOp->eraseFromParent();
                    changed = true;
                  }
                }
              }
            }
          }
        }
      }
    }

    if (changed) {
      return PreservedAnalyses::none();
    }
    return PreservedAnalyses::all();
  }

  static bool isRequired() { return true; }
};
} // anonymous namespace

// ---------------------------------------------------------------------------
// Registrazione dei Pass nel Plugin
// ---------------------------------------------------------------------------
PassPluginLibraryInfo getMyPassesPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "MyPasses", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            // Registriamo i pass come "algebraic-id-pass", "strength-reduction-pass", "multi-instr-pass"
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "algebraic-id-pass") {
                    FPM.addPass(AlgebraicIdentityPass());
                    return true;
                  } else if (Name == "strength-reduction-pass") {
                    FPM.addPass(StrengthReductionPass());
                    return true;
                  } else if (Name == "multi-instr-pass") {
                    FPM.addPass(MultiInstructionOptPass());
                    return true;
                  }
                  return false;
                });
          }};
}

// Dichiarazione C-style per permettere a LLVM di caricare correttamente il plugin
extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return getMyPassesPluginInfo();
}
