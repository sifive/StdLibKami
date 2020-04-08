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
      lenVal : word lgSize;
      lenValL : word (@lgSize ifcParamsL);
      lenValR : word (@lgSize ifcParamsR);
      HimplRegVal : specRegVals = implRegValL ++ implRegValR;
      HnonDetEmpVal : nonDetEmpVal = nonDetEmpValL;
      Ho_sCorrect : o_s =
                    [(GenericSpec.nonDetEmptyName, existT _ (SyntaxKind Bool) nonDetEmpVal);
                    (GenericSpec.listName, existT _ (GenericSpec.nlist type) specRegVals);
                    (GenericSpec.nonDetLenName, existT _ (SyntaxKind (Bit lgSize)) lenVal)];
      Ho_s1Correct : o_s1 =
                     [((@GenericSpec.nonDetEmptyName ifcParamsL),
                       existT _ (SyntaxKind Bool) nonDetEmpValL);
                     ((@GenericSpec.listName ifcParamsL),
                      existT _ (GenericSpec.nlist type) implRegValL);
                     ((@GenericSpec.nonDetLenName ifcParamsL),
                      existT _ (SyntaxKind (Bit lgSize)) lenValL)];
      Ho_s2Correct : o_s2 =
                     [((@GenericSpec.nonDetEmptyName ifcParamsR),
                       existT _ (SyntaxKind Bool) nonDetEmpValR);
                     ((@GenericSpec.listName ifcParamsR),
                      existT _ (GenericSpec.nlist type) implRegValR);
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
    all : unfold EffectfulRelation, EffectlessRelation,
          fifoImpl, fifoSpec, impl, spec,
          isEmpty, isFull, numFree, first, deq, enq, flush,
          GenericSpec.isEmpty, GenericSpec.isFull, GenericSpec.numFree, GenericSpec.first,
          GenericSpec.deq, GenericSpec.enq, GenericSpec.flush,
          DoubleFifo.isEmpty, DoubleFifo.isFull, DoubleFifo.numFree, DoubleFifo.first,
          DoubleFifo.deq, DoubleFifo.enq, DoubleFifo.flush.
    all: intros; try Record_destruct; destruct HCorrectL, HCorrectR;
      cbn [CorrectDef.fifoRegs CorrectDef.fifoR] in *.
    - unfold fifoSpecL, spec, GenericSpec.isEmpty, GenericSpec.numFree in *; cbn [isEmpty] in *.
      hyp_consumer.
      goal_consumer1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x0); simpl.
  (*     hyp_consumer. *)
  (*     goal_consumer1. *)
  (*     unfold GenericSpec.nlist, DoubleFifo.ifcParamsL, k in x1. *)
  (*     rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x1). *)
  (* Admitted. *)
  Admitted.
End Proofs.
