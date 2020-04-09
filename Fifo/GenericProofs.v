Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.CorrectDef.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.GenericSpec.
Require Import StdLibKami.Fifo.DoubleFifo.
Require Import StdLibKami.Fifo.CorrectDef.
Require Import StdLibKami.Fifo.Proofs2.


Definition valsToSnd {k : Kind} (l : list (type k)) :=
  map (fun x => existT (fullType type) (SyntaxKind k)
                       (nth_default (evalConstT Default) l x)) (seq 0 (length l)).

Section Proofs.
  Context {ifcParams : Fifo.Ifc.Params}.
  Context {dblParams : Fifo.DoubleFifo.Params}.

  Local Definition fifoImpl := @Fifo.DoubleFifo.impl ifcParams dblParams.
  Local Definition fifoSpec := @Fifo.GenericSpec.spec ifcParams.
  Local Notation ifcParamsL := (Ifc.Build_Params (append (@name ifcParams) "L")
                                                 (@k ifcParams)
                                                 sizeL).
  Local Notation ifcParamsR := (Ifc.Build_Params (append (@name ifcParams) "R")
                                                 (@k ifcParams)
                                                 sizeR).
  Local Definition fifoSpecL := @Fifo.GenericSpec.spec ifcParamsL.
  Local Definition fifoSpecR := @Fifo.GenericSpec.spec ifcParamsR.
  
  Variable HCorrectL : FifoCorrect Lfifo fifoSpecL.
  Variable HCorrectR : FifoCorrect Rfifo fifoSpecR.
  
  Record myGenFifoR  (o_i o_s : RegsT) : Prop :=
    {
      o_i1 : RegsT;
      o_i2 : RegsT;
      o_s1 : RegsT;
      o_s2 : RegsT;
      implRegsL : RegsT;
      implRegsR : RegsT;
      implRegValL : list (type k);
      implRegValR : list (type k);
      specRegVals : list (type k);
      nonDetEmpVal : bool;
      nonDetEmpValL : bool;
      nonDetEmpValR : bool;
      nonDetFullVal : bool;
      nonDetFullValL : bool;
      nonDetFullValR : bool;
      lenVal : word lgSize;
      lenValL : word (@lgSize ifcParamsL);
      lenValR : word (@lgSize ifcParamsR);
      HlenVal : lenVal = if (wltu lenValL $(sizeL - (length implRegValL))) then
                           $(wordToNat lenValL) else
                           if (Nat.eqb (length implRegValL) 0) then
                             $(sizeL + (wordToNat lenValR)) else
                             $(sizeL - (length implRegValL));
      HimplRegVal : specRegVals = implRegValL ++ implRegValR;
      HnonDetEmpVal : nonDetEmpVal = (nonDetEmpValR || negb (emptyb implRegValL));
      Ho_sCorrect : o_s =
                    [(GenericSpec.nonDetEmptyName, existT _ (SyntaxKind Bool) nonDetEmpVal);
                    (GenericSpec.nonDetFullName, existT _ (SyntaxKind Bool) nonDetFullVal);
                    (GenericSpec.listName, existT _ GenericSpec.nlist specRegVals);
                    (GenericSpec.nonDetLenName, existT _ (SyntaxKind (Bit lgSize)) lenVal)];
      Ho_s1Correct : o_s1 =
                     [((@GenericSpec.nonDetEmptyName ifcParamsL),
                       existT _ (SyntaxKind Bool) nonDetEmpValL);
                     ((@GenericSpec.nonDetFullName ifcParamsL),
                     existT _ (SyntaxKind Bool) nonDetFullValL);
                     ((@GenericSpec.listName ifcParamsL),
                      existT _ GenericSpec.nlist implRegValL);
                     ((@GenericSpec.nonDetLenName ifcParamsL),
                      existT _ (SyntaxKind (Bit lgSize)) lenValL)];
      Ho_s2Correct : o_s2 =
                     [((@GenericSpec.nonDetEmptyName ifcParamsR),
                       existT _ (SyntaxKind Bool) nonDetEmpValR);
                     ((@GenericSpec.nonDetFullName ifcParamsR),
                     existT _ (SyntaxKind Bool) nonDetFullValR);
                     ((@GenericSpec.listName ifcParamsR),
                      existT _ GenericSpec.nlist implRegValR);
                     ((@GenericSpec.nonDetLenName ifcParamsR),
                      existT _ (SyntaxKind (Bit lgSize)) lenValR)];
      Ho_iApp : o_i = o_i1 ++ o_i2;
      HRegs1 : getKindAttr o_i1 = (fifoRegs HCorrectL);
      HRegs2 : getKindAttr o_i2 = (fifoRegs HCorrectR);
      HfifoR1 : (fifoR HCorrectL) o_i1 o_s1;
      HfifoR2 : (fifoR HCorrectR) o_i2 o_s2;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.

  Ltac Record_destruct :=
    match goal with
    | [H : myGenFifoR _ _ |- _] =>
      destruct H
    end.

  Goal FifoCorrect fifoImpl fifoSpec.
    destruct HCorrectL, HCorrectR.
    econstructor 1 with (fifoR := myGenFifoR)
                        (fifoRegs := fifoRegs ++ fifoRegs0).
    all : unfold EffectfulRelation, EffectlessRelation, ActionWb,
          fifoImpl, fifoSpec, impl, spec,
          isEmpty, isFull, numFree, first, deq, enq, flush,
          GenericSpec.isEmpty, GenericSpec.isFull, GenericSpec.numFree, GenericSpec.first,
          GenericSpec.deq, GenericSpec.enq, GenericSpec.flush,
          DoubleFifo.isEmpty, DoubleFifo.isFull, DoubleFifo.numFree, DoubleFifo.first,
          DoubleFifo.deq, DoubleFifo.enq, DoubleFifo.flush.
    all: intros; try Record_destruct; destruct HCorrectL, HCorrectR;
      cbn [CorrectDef.fifoRegs CorrectDef.fifoR] in *;
      unfold fifoSpecR, fifoSpecL, spec,  GenericSpec.enq, GenericSpec.deq,
      GenericSpec.first, GenericSpec.isEmpty,
      GenericSpec.isFull, GenericSpec.flush, GenericSpec.numFree in *;
      cbn [isEmpty isFull flush enq deq first numFree] in *;
        unfold GenericSpec.nonDetFullName, GenericSpec.nonDetEmptyName in *.
    - hyp_consumer.
      + goal_consumer1.
        rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0); simpl.
        admit.
      + exfalso.
        apply append_remove_prefix in H0; discriminate.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + exfalso.
        unfold GenericSpec.nonDetEmptyName, GenericSpec.nonDetFullName in H0.
        apply append_remove_prefix in H0; discriminate.
      + goal_consumer1.
        rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0); simpl.
        admit.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x1), (Eqdep.EqdepTheory.UIP_refl _ _ x3); simpl.
      repeat rewrite evalExpr_castBits; simpl.
      admit.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + goal_consumer1.
        admit.
      + exfalso.
        apply append_remove_prefix in H6; discriminate.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + goal_consumer1.
        * admit.
        * admit.
      + exfalso.
        apply append_remove_prefix in H6; discriminate.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      + exfalso.
        apply append_remove_prefix in H6; discriminate.
      + goal_consumer1.
        * admit.
        * admit.
    - hyp_consumer.
      goal_consumer2.
    - hyp_consumer.
      goal_consumer1.
      admit.
    - hyp_consumer.
      goal_consumer2.
  Admitted.
End Proofs.
