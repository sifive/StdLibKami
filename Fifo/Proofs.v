Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.

Record FifoCorrect {FParams} (imp spec : @Fifo.Ifc.Ifc FParams) : Type :=
  {
    fifoRegs : list (Attribute FullKind);
    fifoR : RegsT -> RegsT -> Prop;
    isEmptyCorrect : EffectlessRelation fifoR (@isEmpty _ imp type) (@isEmpty _ spec type);
    isEmptyWb : ActionWb fifoRegs (@isEmpty _ imp type);
    isFullCorrect : EffectlessRelation fifoR (@isFull _ imp type) (@isFull _ spec type);
    isFullWb : ActionWb fifoRegs (@isFull _ imp type);
    numFreeCorrect : EffectlessRelation fifoR (@numFree _ imp type) (@numFree _ spec type);
    numFreeWb : ActionWb fifoRegs (@numFree _ imp type);
    firstCorrect : EffectfulRelation fifoR (@first _ imp type) (@first _ spec type);
    firstWb : ActionWb fifoRegs (@first _ imp type);
    deqCorrect : EffectfulRelation fifoR (@deq _ imp type) (@deq _ spec type);
    deqWb : ActionWb fifoRegs (@deq _ imp type);
    enqCorrect : forall val, EffectfulRelation fifoR (@enq _ imp type val) (@enq _ spec type val);
    enqWb : forall val, ActionWb fifoRegs (@enq _ imp type val);
    flushCorrect : EffectlessRelation fifoR (@flush _ imp type) (@flush _ spec type);
  }.

Section Proofs.
  Context {ifcParams' : Fifo.Ifc.Params}.
  Context `{implParams : @Impl.Params ifcParams'}.
  Context `{specParams : @Spec.Params ifcParams'}.
  Definition implFifo := @impl ifcParams' implParams.
  Definition specFifo := @spec ifcParams'.

  Variable implRegs : RegsT.
  Variable deqVal enqVal : word (Fifo.Ifc.lgSize + 1).
  Variable specRegs : RegT.
  Variable listVal : list (type Fifo.Ifc.k).
    
  Record myFifoImplR (o_i o_s : RegsT) : Prop :=
    {
      implRegVal : implRegs = [(Fifo.Impl.deqPtrName, existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) deqVal);
                              (Fifo.Impl.enqPtrName, existT _ (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))) enqVal)];
      specRegVal : specRegs = (Fifo.Spec.listName, existT _ (Fifo.Spec.nlist type) listVal);
      Ho_iCorrect : o_i = implRegs;
      Ho_sCorrect : o_s = [specRegs];
      Ho_iNoDup : NoDup (map fst o_i);
    }.

  Ltac Record_destruct :=
    match goal with
    |[ H : myFifoImplR _ _ |- _] => destruct H
    end.

  Goal FifoCorrect implFifo specFifo.
    econstructor 1 with (fifoR := myFifoImplR) (fifoRegs := [(Fifo.Impl.deqPtrName, (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))));
                                                             (Fifo.Impl.enqPtrName, (SyntaxKind (Bit (Fifo.Ifc.lgSize + 1))))]).
    all : red; unfold implFifo, impl, specFifo, spec, regArray,
               isEmpty, flush, enq, deq, numFree, isFull, first,
               Impl.isEmpty, Impl.flush, Impl.enq, Impl.deq, Impl.numFree, Impl.isFull, Impl.first,
               Spec.isEmpty, Spec.flush, Spec.enq, Spec.deq, Spec.numFree, Spec.isFull, Spec.first.
    all : unfold Impl.isEmpty, Impl.fastModSize.
    all : unfold Ifc.read; intros; try Record_destruct; hyp_consumer1.
  Admitted.
End Proofs.
