#include "llvm/Transforms/Utils/LoopFusion.h"
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Dominators.h>
#include <llvm/ADT/DepthFirstIterator.h>
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
using namespace llvm;

// Funzione di supporto che stabilisce se dati due loop Lj e Lk sono ADIACENTI tra loro (supponendo Lj < Lk)
bool areAdjacent(Loop *Lj, Loop* Lk){
  BasicBlock *exitBlockL1 = Lj->getExitBlock();
  BasicBlock *preHeaderL2 = Lk->getLoopPreheader();

  const Instruction *terminator = exitBlockL1->getTerminator();

  if (terminator->getSuccessor(0) == preHeaderL2)
    return true;

  return false;
}

// Funzione di supporto per controllare se il loop Lj e Lk siano equivalenti dal punto di vista del flusso di esecuzione
bool areControlFlowEquivalent(Loop *Lj, Loop *Lk, DominatorTree &DT, PostDominatorTree &PDT) {
  // Verifica se l'header di Lj domina l'header di Lk
  if (!DT.dominates(Lj->getLoopPreheader(), Lk->getLoopPreheader())) {
    outs() << "Lj non domina Lk\n";
    return false;
  }
    
  // Verifica se l'header di Lk post-domina l'header di Lj
  if (!PDT.dominates(Lk->getLoopPreheader(), Lj->getLoopPreheader())) {
    outs() << "Lk non post-domina Lj\n";
    return false;
  }

  return true; // Lj e Lk sono control flow equivalent
}

// Funzione di supporto che controlla se i due loop hanno lo stesso spazio di iterazione
bool sameTripCount(Loop *Lj, Loop *Lk, ScalarEvolution &SE){
  //const SCEV *tripCountJ = SE.getBackedgeTakenCount(Lj);
  //const SCEV *tripCountK = SE.getBackedgeTakenCount(Lk);
  const int tripCountJ = SE.getSmallConstantTripCount(Lj);
  const int tripCountK = SE.getSmallConstantTripCount(Lk);

  outs() << "Trip count Lj: " << tripCountJ << "\n";
  outs() << "Trip count Lk: " << tripCountK << "\n";
  
  if (tripCountJ == tripCountK)
    return true;

  return false;
}

bool hasNegativeDependencies(Loop *Lj, Loop *Lk, DependenceInfo &DA){
  // Itero per tutti i Basic Block del loop Lj
  for (auto *BBj : Lj->getBlocks()){
    // Itero per tutte le istruzioni nel Basic Block del loop Lj
    for (auto &Ij : *BBj){
      // Itero per tutti i Basic Block del loop Lk
      for (auto *BBk : Lk->getBlocks()){
        // Itero per tutte le istruzioni nel Basic Block del loop Lk
        for (auto &Ik : *BBk){
          // Verifico se esiste una dipendenza tra le due istruzioni
          if (auto dep = DA.depends(&Ij, &Ik, true)){ // se non vi è dipendenza, allora ritornerà null
            // Verifichiamo se vi è una DIPENDENZA NEGATIVA
            outs() << "C'è una dipendenza tra l'istruzione ij: "<< Ij << " e l'istruzione ik: "<< Ik << "\n";

            // Verifico se è una dipendenza negativa
            if (dep->isAnti()){
              outs() << "La dipendenza è negativa\n";
              return true;
            }

          }
        }
      }
    }
  }

  return false; // Nessuna dipendenza a distanza negativa trovata
}

// Funzione di supporto che verifica se tutte le condizioni per la loop fusion siano garantite
bool canFuseLoops(Loop *Lj, Loop *Lk, LoopInfo &LI, DominatorTree &DT, PostDominatorTree &PDT, ScalarEvolution &SE, DependenceInfo &DI) {
  // Condizione 1: Lj e Lk devono essere adiacenti
  if (!areAdjacent(Lj, Lk)) {
    outs() << "Non sono adiacenti\n";
    return false;
  }

  // Condizione 2: Lj e Lk devono iterare lo stesso numero di volte
  if (!sameTripCount(Lj, Lk, SE)) {
    outs() << "Non hanno lo stesso numero di iterazioni\n";
    return false;
  }

  // Condizione 3: Lj e Lk devono essere equivalenti nel flusso di controllo
  if (!areControlFlowEquivalent(Lj, Lk, DT, PDT)){
    outs() << "Non sono control flow equivalent\n";
    return false;
  }
  
  // Condizione 4: Non ci devono essere dipendenze a distanza negativa
  if (hasNegativeDependencies(Lj, Lk, DI)) return false;

  return true;
}

void fuseLoops(Loop *Lj, Loop *Lk, LoopInfo &LI, ScalarEvolution &SE, DominatorTree &DT){
  outs() << "----INIZIO LA FUSIONE DEI DUE LOOP----\n";

  // PASSO 1: modificare gli usi delle induction varaible nel body del loop 2 con quelli
  // della induction variable del loop 1

  // Cerco le variabili di induzione dei due loop
  PHINode *IV1 = Lj->getCanonicalInductionVariable(); 
  PHINode *IV2 = Lk->getCanonicalInductionVariable();

  outs() << "1. Cerco le variabili di induzione...\n";

  if (!IV1) {
    outs() << "Impossibile trovare la variabile di induzione di lj.\n";
    return;
  }
  if (!IV2) {
    outs() << "Impossibile trovare la variabile di induzione di lk.\n";
    return;
  }

  outs() << "Variabili di induzione trovate\n";

  outs() << "2. Modifico gli usi delle variabili di induzione del secondo ciclo con quelle del primo ciclo...\n";

  // Sostituire gli usi della variabile di induzione del loop k (il secondo loop)
  for (auto *BB : Lk->blocks()) {
    for (auto &I : *BB) {
      // Per tutti gli operandi dell'istruzione nel Basic Block considerato
      for (auto &Op : I.operands()) { 
        // Se l'operando coincide con la induction var. del loop 2, allora sostituisco l'uso con quella del primo loop
        if (Op == IV2)  
          Op.set(IV1); // Sostituisco l'uso di IV2 con IV1
        }
      }
  }
  
  outs() << "Variabili di induzione cambiate\n";

  // PASSO 2: modifico il Control Flow Graph
  outs() << "3. Inizio modifica del Control Flow Graph...\n";

  // Prelevo i Basic Block di cui ho bisogno per il passo 2
  // Loop 1
  BasicBlock *latchL1 = (*Lj).getLoopLatch();
  BasicBlock *endBodyL1 = (*latchL1).getPrevNode();
  Instruction *bodyTerminatorL1 = (*endBodyL1).getTerminator();
  BasicBlock *headerL1 = (*Lj).getHeader();
  Instruction *headerTerminatorL1 = (*headerL1).getTerminator();

  // Loop 2
  BasicBlock *latchL2 = (*Lk).getLoopLatch();
  BasicBlock *endBodyL2 = (*latchL2).getPrevNode();
  Instruction *bodyTerminatorL2 = (*endBodyL2).getTerminator();
  BasicBlock *headerL2 = (*Lk).getHeader();
  BasicBlock *beginBodyL2 = (*headerL2).getNextNode();
  BasicBlock *exitBlockL2 = (*Lk).getExitBlock();
  Instruction *headerTerminatorL2 = (*headerL2).getTerminator();

  // PASSO 2.1: connetto il body del loop Lj con il body del loop Lk
  outs() << "3.1. Connetto il body del loop 1 con il body del loop 2...\n";

  (*bodyTerminatorL1).setSuccessor(0, beginBodyL2);

  outs() << "Aggancio dei due body effettuato\n";

  // PASSO 2.2: connetto il body del loop Lk con il latch del loop Lj
  outs() << "3.2. Connetto il body del loop 2 con il latch del loop 1...\n";

  (*bodyTerminatorL2).setSuccessor(0, latchL1);

  outs() << "Aggancio body l2 e latch l1 effettuato\n";

  // PASSO 2.3: l'exit block del loop 1 diventa l'exit block del loop 2
  outs() << "3.3. Sostituisco l'exit block del loop 2 con l'exit block del loop 1...\n";

  (*headerTerminatorL1).setSuccessor(1, exitBlockL2);

  outs() << "Modifica dell'exit block effettuata\n";

  // PASSO 2.4: l'header del loop 2 viene connesso al latch del loop 2
  outs() << "3.4. Aggancio dell'header del loop 2 con il latch del loop 2...\n";

  (*headerTerminatorL2).setSuccessor(0, latchL2);

  outs() << "Aggancio dell'header effetuato\n";

  outs() << "----FINE DELLA FUSIONE DEI DUE LOOP----\n";
}

PreservedAnalyses LoopFusion::run(Function &F, FunctionAnalysisManager &FAM) {
  LoopInfo &LI = FAM.getResult<LoopAnalysis>(F);
  DominatorTree &DT = FAM.getResult<DominatorTreeAnalysis>(F);
  PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
  ScalarEvolution &SE = FAM.getResult<ScalarEvolutionAnalysis>(F);
  DependenceInfo &DI = FAM.getResult<DependenceAnalysis>(F);

  // SmalVector contenente tutti i loop della funzione
  SmallVector<Loop*> loops = LI.getLoopsInPreorder();

  outs() << "----INIZIO PASSO LOOP FUSION----\n";
  for (auto &iterLoop1 : loops){
    for (auto &iterLoop2 : loops) {
      if (iterLoop1 != iterLoop2){
        Loop *L1 = iterLoop1;
        Loop *L2 = iterLoop2;
        if (canFuseLoops(L1, L2, LI, DT, PDT, SE, DI))
          fuseLoops(L1, L2, LI, SE, DT);
      }
    }
  }
 
  return PreservedAnalyses::all();
}


