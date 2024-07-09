#include "llvm/Transforms/Utils/LoopWalk2.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/GenericLoopInfo.h"
#include "llvm/ADT/SmallVector.h"

using namespace llvm;

// Funzione di supporto che stabilisce se una data istruzione è loop-invariant
bool isLoopInvariant(Loop& L, const std::vector <Instruction*> &invariantInstructions, Instruction& Inst) {
    // Variabile di supporto per il check del loop invariant
	bool isInvariant = true;

    // Itero per ogni operatore dell'istruzione
	for (auto* Iter = Inst.op_begin(); Iter != Inst.op_end(); ++Iter) {
		// Ottengo l'operando
		Value* Operand = *Iter;

        // Controllo se l'operando op è una costante, allora potrebbe essere invariant
		if (ConstantInt* C = dyn_cast<ConstantInt>(Operand)) { 
			isInvariant = true; 
		}
		else if (Instruction* I = dyn_cast<Instruction>(Operand)) { //controllo l'istruzione generatrice
            // Se non è costante, allora bisogna ragionare su due casi
            // CASO 1: per ogni istruzione del tipo A = B + C l'istruzione è loop-invariant
            // se Tutte le definizioni di B e C che raggiungono l’istruzione A = B + C si trovano FUORI dal loop
            // CASO 2: c’è esattamente una reaching definition per B (e C), e si tratta di un’istruzione del loop che è stata 
            // marcata loop-invariant

            // CASO 1: Controllo se il Basic Block padre è nel Loop
			// Ottengo il Basic Block dell'istruzione e controllo se è nel loop
			if (L.contains(I->getParent())) {
				isInvariant = false; 

                // CASO 2
                // Scorro per tutte le istruzioni nel vettore invariantInstructions
				for (const Instruction* inst : invariantInstructions) {
					if (inst == I) 
						isInvariant = true; 	
				}
			}
			else
				isInvariant = true;
		}
		if (!isInvariant)
			return false;
	}
	return true;
}

// Funzione di supporto che ritorna true se basicBlock domina tutti i basic blocks di uscita dal loop
bool dominatesAllExit(BasicBlock* basicBlock, const SmallVector<BasicBlock*>& exitLoopBlocks, DominatorTree& DT){
    // Per ogni basic block fuori dal loop (memorizzato nello smal vector)
    for (auto *basicBlockExit : exitLoopBlocks){
        // Se basic block non domina anche uno solo di uscita, allora ritorno false
        if(!DT.properlyDominates(basicBlock, basicBlockExit))
            return false;
    }

    // basic block domina tutti i basic blocks di uscita del loop
    return true;
}

// Funzione di supporto che ritorna true se l'istruzione candidata domina tutti i blochi nel loop
// che usano la variabile a cui si sta assegnando un valore
bool dominatesAllUses(Instruction* inst, Loop& L, DominatorTree& DT){
    BasicBlock* basicBlock = inst->getParent();
    Value* assignedValue = inst;
    
    // Scorro per tutti gli user che usa l'istruzione I
    for(auto *user : assignedValue->users()){
        if (Instruction* userInst = dyn_cast<Instruction>(user)){
            // Prendo il basic block in cui è definita l'istruzione user
            BasicBlock* userBB = userInst->getParent();

            // Controllo se il basic block dell'uso è contenuto nel loop
            if (L.contains(userBB)){
                // Verifichiamo se il blocco basicBlock domina il blocco dell'uso
                if (!DT.properlyDominates(basicBlock, userBB))
                    return false;
            }
        }
    }

    // Se tutto è andato a buon file, allora posso ritornare true
    return true;
}

// Funzione di supporto che stabilisce se una istruzione candidata possa essere effettivamente spostata nel preheader
bool allDependenciesMoved(Instruction* inst, std::vector<Instruction*>& candidateInst, Loop& L){
    // Per ogni operando dell'istruzione
    for (Value* op : inst->operands()){
        if (Instruction* opInst = dyn_cast<Instruction>(op)){
            bool found = false;
            // Controllo se l'istruzione è nel loop
            if (L.contains(opInst)){
                // Controlliamo se l'istruzione è da spostare (deve appartenere al vettore)
                for (auto *inst : candidateInst){
                    if (inst == opInst){
                        found = true;
                        break; // L'istruzione è stata trovata, si procede con il prossimo operando
                    }
                }

                if (!found)
                    return false;
            }
        }
    }

    return true;
}

bool runOnLoop2(Loop &L, LoopAnalysisManager &LAM, LoopStandardAnalysisResults &LAR, LPMUpdater &LU) {
    // PASSO 1
    // Controllo se il loop è nella forma NORMALIZZATA
    if (!L.isLoopSimplifyForm()) {
        errs() << "Il loop non è in forma normalizzata\n";
        return false;
    }

    // PASSO 2: identifico tutte le istruzioni loop-invariant

    // Vettore di istruzioni che memorizza le istruzioni loop-invariant
    std::vector <Instruction*> invariantInstructions;

    // Itero sui basic block del loop
    int i = 1; // Per contare i blocchi
    for (auto blockIterator = L.block_begin(); blockIterator != L.block_end(); ++blockIterator) {
        BasicBlock *BasicBlock = *blockIterator;
        outs() << "Blocco" << i << "\n";

        // Itero per ogni istruzione nel basic block
        for (auto &inst : *BasicBlock) {
            outs() << inst << "\n";  

            // Controllo se inst è una loop-invariant
            if (isLoopInvariant(L, invariantInstructions, inst))       
                invariantInstructions.push_back(&inst);                                                          
        }

        i++;
    }

    // Stampa di debug delle istruzioni invariant
    outs() << "---STAMPA ISTRUZIONI INVARIANT IDENTIFICATE---\n";
    for (auto *inst : invariantInstructions){
        outs() <<"Istruzione: "<< *inst << "\n";
    }

    // PASSO 3: identifico le istruzioni candidate alla code-motion
    // Tra tutte le possibili istruzioni loop-invariant quelle candidate alla code motion sono quelle:
    // - loop invariant
    // - si trovano in blocchi che dominano tutte le uscite del loop
    // - assegnano un valore a variabili non assegnate altrove nel loop
    // - si trovano in blocchi che dominano tutti i blocchi nel loop che usano la variabile
    //   a cui si sta assegnando un valore

    // Vettore che memorizza le istruzioni candidate alla code-motion
    std::vector <Instruction*> candidateInst;

    // Dominance Tree
    DominatorTree &DT = LAR.DT;

    // Vettore che memorizza i basic blocks di uscita del loop
    SmallVector<BasicBlock*> exitLoopBlocks;
	L.getExitBlocks(exitLoopBlocks);

    for (auto *inst : invariantInstructions){
        // Ottengo il basic block in sui si trova l'istruzione
        BasicBlock* basicBlock = inst->getParent();

        // Controllo se basicBlock domina tutte le USCITE e gli USI
        if (dominatesAllExit(basicBlock, exitLoopBlocks, DT) && dominatesAllUses(inst, L, DT))
            candidateInst.push_back(inst);
    }

    // Stampa di debug delle istruzioni candidate alla code-motion
    outs() <<"---STAMPA ISTRUZIONI CANDIDATE ALLA CODE MOTION---\n";
    for (auto *inst : candidateInst){
        outs() <<"Istruzione: "<< *inst << "\n";
    }

    // PASSO 4: spostiamo le istruzioni candidate alla code-motion nel PREHEADER a patto che vengano rispettate le dipendende
    // tutte le istruzioni invarianti da cui questa dipende devono essere spostate

    BasicBlock *preHeader = L.getLoopPreheader();
    if (!preHeader) {
        outs() << "Preheader non trovato\n";
        return false;
    }
    
    // Per ogni istruzione candidata cerco se il vincolo è rispettato
    for (auto *inst : candidateInst){
        if (allDependenciesMoved(inst, candidateInst, L)){
            // Il vincolo è rispettato, dunque sposto l'istruzione alla fine del preheader
            outs() << "L'istruzione "<< *inst << " può essere spostata nel preheader\n";
            inst->moveBefore(preHeader->getTerminator());
        }     
    }
    return true;
}

PreservedAnalyses LoopWalk2::run(Loop &L, LoopAnalysisManager &LAM, LoopStandardAnalysisResults &LAR, LPMUpdater &LU) {
    outs() << "---INIZIO PASSO LOOP---\n";
    if (runOnLoop2(L, LAM, LAR, LU)) {
        return PreservedAnalyses::all();
    } else {
        return PreservedAnalyses::none();
    }                                               
}