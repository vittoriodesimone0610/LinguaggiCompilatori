//===-- LocalOpts.cpp - Example Transformations --------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/LocalOpts2.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/ADT/APInt.h"

#include <stack>

using namespace llvm;

bool runOnBasicBlock2(BasicBlock &B) {
    LLVMContext &context = B.getContext();
    IRBuilder<> Builder(context);

    // Lo stack serve per memorizzare le istruzioni da ELIMINARE
    std::stack<Instruction*> delStack;

    // Le variabili seguenti servono come indice di controllo
    int strength_reduction_count = 0;
    int algebraic_identity_count = 0;
    int multi_instr_opt_count = 0;

    outs() << "---Iterazione su tutte le istruzioni nel Basic Block:---\n";
    for (Instruction &instIter : B) {
        Instruction *I = &instIter;
        outs() << "Istruzione: " << instIter << "\n";

        // Controllo se sia una operazione binaria
        if (auto *binOp = dyn_cast<BinaryOperator>(I)) {
            Value *op1 = binOp->getOperand(0);
            Value *op2 = binOp->getOperand(1);

            // Controllo se uno dei due operandi è COSTANTE
            ConstantInt *x = dyn_cast<ConstantInt>(op1);
            ConstantInt *y = dyn_cast<ConstantInt>(op2);

            // Se entrambe le costanti sono nulle, ignora l'istruzione
            if (!x && !y) {
                continue;
            }

            if (binOp->getOpcode() == Instruction::Mul) { // L'istruzione è una MOLTIPIPLICAZIONE
                if (x != nullptr) {
                    outs() << "L'operando " << *x << " è costante\n";

                    // PASSO 1.2 - SLIDE 05
                    // Controllo se il valore costante è pari a 1 -> algebraic identity
                    if (x->isOne()){
                        outs() <<"L'operando "<< *x <<" vale 1\n";
                        I->replaceAllUsesWith(op2);
                        delStack.push(I);

                        outs() << "Applicata algebraic identity\n";
                        algebraic_identity_count++;
                    }
                    else{ // Caso della strength reduction
                        APInt val = x->getValue();

                        // Se il valore della costante x è una potenza di 2, allora è candidata per lo shift
                        if (val.isPowerOf2()) {
                            // Creo una nuova costante per definire di quanto sarà lo shift (log base 2 di val)
                            ConstantInt *constantShift = ConstantInt::get(Type::getInt32Ty(context), val.logBase2());

                            outs() <<"L'operaando "<< *x <<" è una potenza di 2\n";

                            // Creo la nuova istruzione di shift
                            Instruction *newInst = BinaryOperator::Create(Instruction::Shl, op2, constantShift);

                            // Rimpiazzo e aggiorno gli usi
                            newInst->insertAfter(&instIter);
                            I->replaceAllUsesWith(newInst);
                            delStack.push(I);

                            outs() << "Applicata strength reduction\n";
                            strength_reduction_count++;
                        }
                        else{
                            // Calcolo il valore del log più vicino (sotraggo 1 perché viene arrotondato sempre per eccesso)
                            Value* constantShift = Builder.getInt32(val.nearestLogBase2()-1);

                            // Creo l'istruzione di shift
                            Instruction *newInstShl = BinaryOperator::Create(Instruction::Shl, op2, constantShift);

                            // Creo l'istruzione di sottrazione
                            Instruction *newInstSub = BinaryOperator::Create(Instruction::Sub, newInstShl, op2);

                            // Rimpiazzo e aggiorno gli usi
                            newInstShl->insertAfter(&instIter);
                            newInstSub->insertAfter(newInstShl);
                            I->replaceAllUsesWith(newInstSub);
                            delStack.push(I);

                            outs() << "Applicata strength reduction\n";
                            strength_reduction_count++;
                        }
                    }   
                } 
                else if (y != nullptr) {
                    if (y->isOne()){
                        outs() <<"L'operando "<< *y <<" vale 1\n";
                        I->replaceAllUsesWith(op1);
                        delStack.push(I);

                        outs() << "Applicata algebraic identity\n";
                        algebraic_identity_count++;
                    }
                    else{
                        APInt val = y->getValue();
                        outs() << "L'operando " << *y << " è costante\n";

                        // Se il valore della costante y è una potenza di 2, allora è candidata per lo shift
                        if (val.isPowerOf2()) {
                            // Creo una nuova costante per definire di quanto sarà lo shift (log base 2 di val)
                            ConstantInt *constantShift = ConstantInt::get(Type::getInt32Ty(context), val.logBase2());

                            outs() <<"L'operando "<< *y <<" è una potenza di 2\n";
                            // Creo la nuova istruzione di shift
                            Instruction *newInst = BinaryOperator::Create(Instruction::Shl, op1, constantShift);

                            // Rimpiazzo e aggiorno gli usi
                            newInst->insertAfter(&instIter);
                            I->replaceAllUsesWith(newInst);
                            delStack.push(I);

                            outs() << "Applicata strength reduction\n";
                            strength_reduction_count++;
                        }
                        else{
                            // Calcolo il valore del log più vicino (sotraggo 1 perché viene arrotondato sempre per eccesso)
                            Value* constantShift = Builder.getInt32(val.nearestLogBase2()-1);

                            // Creo l'istruzione di shift
                            Instruction *newInstShl = BinaryOperator::Create(Instruction::Shl, op1, constantShift);

                            // Creo l'istruzione di sottrazione
                            Instruction *newInstSub = BinaryOperator::Create(Instruction::Sub, newInstShl, op1);

                            // Rimpiazzo e aggiorno gli usi
                            newInstShl->insertAfter(&instIter);
                            newInstSub->insertAfter(newInstShl);
                            I->replaceAllUsesWith(newInstSub);
                            delStack.push(I);

                            outs() << "Applicata strength reduction\n";
                            strength_reduction_count++;
                        }
                    }
                }
            }// Fine if per binary instruction mul
            else if (binOp->getOpcode() == Instruction::Add){ // L'istruzione è una ADDIZIONE
                // PASSO 1.1 - SLIDE 05
                // Controllo se siamo nel caso della ALGEBRAIC IDENTIITY: x + 0 = 0 + x = x
                if (x != nullptr){
                    outs() << "L'operando " << *x << " è costante\n";

                    if (x->isZero()){
                        outs() << "L'operando "<< *x << " vale 0\n";

                        I->replaceAllUsesWith(op2);
                        delStack.push(I);

                        outs() << "Applicata algebraic identity\n";
                        algebraic_identity_count++;
                    }
                }
                else if (y != nullptr){
                    outs() << "L'operando " << *y << " è costante\n";

                    if (y->isZero()){
                        outs() << "L'operando "<< *y << " vale 0\n";

                        I->replaceAllUsesWith(op1);
                        delStack.push(I);

                        outs() << "Applicata algebraic identity\n";
                        algebraic_identity_count++;
                    } 
                    // PUNTO 3 - SLIDE 05
                    // Dobbiamo trovare delle istruzioni in cui sia possibile applicare la MULTI INSTRUCTION OPTIMIZATION
                    // a = b + 1, c = a -1 -> a = b + 1, c = b   
                    else{
                        // Scorro per tutti gli user
                        for (auto userIter = I->user_begin(); userIter != I->user_end(); ++userIter){
                            if (Instruction *userInst = dyn_cast<Instruction>(*userIter)){
                                // Controllo che esta una istruzione SUB del tipo c = a - 1
                                if (userInst->getOpcode() == Instruction::Sub){
                                    outs() << "Primo operando: "<<*(userInst->getOperand(0))<<"\n";
                                    if (userInst->getOperand(0) == I){
                                        if (ConstantInt *constUser = dyn_cast<ConstantInt>(userInst->getOperand(1))){
                                            if (y->equalsInt(constUser->getZExtValue())){
                                                // Sostituisco userInst con l'operando di instIter
                                                userInst->replaceAllUsesWith(I->getOperand(0));
                                                
                                                outs() << "Applicata Multi-Instruction Opt\n";
                                                multi_instr_opt_count++;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            } // Fine if per binary instruction add
            else if (binOp->getOpcode() == Instruction::SDiv){ // L'istruzione è una DIVISIONE
                // PUNTO 2.2 - SLIDE 05
                // STRENGTH REDUCTION: x/8 = x >> 3
                if (y != nullptr){
                    APInt val = y->getValue();

                    // Se val è una potenza del 2, allora posso applicare la strength reduction
                    if (val.isPowerOf2()){
                        ConstantInt *constantShift = ConstantInt::get(Type::getInt32Ty(context), val.logBase2());

                        // Creo la nuova istruzione di shift verso destra
                        Instruction *newInst = BinaryOperator::Create(Instruction::LShr, op1, constantShift);

                        // Rimpiazzo e aggiorno gli usi
                        newInst->insertAfter(&instIter);
                        I->replaceAllUsesWith(newInst);
                        delStack.push(I);

                        outs() << "Applicata strength reduction\n";
                        strength_reduction_count++;
                    }
                }
            } // Fine if per binary instruction div         
        }
    }

    outs() << "---Inizio eliminazione istruzioni---\n";
    while (!delStack.empty()) {
        outs() << "Elimino l'istruzione: "<< *(delStack.top()) <<"\n";
        delStack.top()->eraseFromParent();
        delStack.pop();
    }

    // Stampe di controllo delle variabili contatore
    outs() << "Strength Reduction applicate: "<< strength_reduction_count << "\n";
    outs() << "Algebraic Identity applicate: "<< algebraic_identity_count << "\n";
    outs() << "Multi-Instruction Optimization applicate: "<< multi_instr_opt_count << "\n";

    return true;
}

bool runOnFunction2(Function &F) {
    bool Transformed = false;

    for (auto Iter = F.begin(); Iter != F.end(); ++Iter) {
        if (runOnBasicBlock2(*Iter)) {
            Transformed = true;
        }
    }

    return Transformed;
}

PreservedAnalyses LocalOpts2::run(Module &M,
                                 ModuleAnalysisManager &AM) {
    for (auto Fiter = M.begin(); Fiter != M.end(); ++Fiter)
        if (runOnFunction2(*Fiter))
            return PreservedAnalyses::none();

    return PreservedAnalyses::all();
}
