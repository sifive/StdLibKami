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
  Local Definition fifoSpecL := @Fifo.GenericSpec.spec (@Fifo.DoubleFifo.ifcParamsL ifcParams).
  Local Definition fifoSpecR := @Fifo.GenericSpec.spec (@Fifo.DoubleFifo.ifcParamsR ifcParams).
  
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
      lenVal : word lgSize;
      lenValL : word (@lgSize (@Fifo.DoubleFifo.ifcParamsL ifcParams));
      lenValR : word (@lgSize (@Fifo.DoubleFifo.ifcParamsR ifcParams));
      HimplRegValL : specRegVals = implRegValL ++ implRegValR;
      HnonDetEmpVal : nonDetEmpVal = nonDetEmpValL;
      Ho_sCorrect : o_s =
                    [(GenericSpec.nonDetEmptyName, existT _ (SyntaxKind Bool) nonDetEmpVal);
                    (GenericSpec.listName, existT _ (GenericSpec.nlist type) specRegVals);
                    (GenericSpec.nonDetLenName, existT _ (SyntaxKind (Bit lgSize)) lenVal)];
      Ho_s1Correct : o_s1 =
                    [((@GenericSpec.nonDetEmptyName (@Fifo.DoubleFifo.ifcParamsL ifcParams)), existT _ (SyntaxKind Bool) nonDetEmpVal);
                    ((@GenericSpec.listName (@Fifo.DoubleFifo.ifcParamsL ifcParams)), existT _ (GenericSpec.nlist type) specRegVals);
                    ((@GenericSpec.nonDetLenName (@Fifo.DoubleFifo.ifcParamsL ifcParams)), existT _ (SyntaxKind (Bit lgSize)) lenVal)];
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
      unfold GenericSpec.nlist, DoubleFifo.ifcParamsL, k in x1.
      rewrite (Eqdep.EqdepTheory.UIP_refl _ _ x1).
  Admitted.
  
End Proofs.
