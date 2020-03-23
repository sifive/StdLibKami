Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.
Require Import StdLibKami.Fifo.Spec.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.

Local Definition isEmpty_impl1 (varName : string) :=
  (Read val : Bool <- varName; Ret (! Var type (SyntaxKind Bool) val))%kami_action.

Local Definition isFull_impl1 (varName : string) :=
  (Read val : Bool <- varName; Ret Var type (SyntaxKind Bool) val)%kami_action.

Local Definition numFree_impl1 (varName : string) (size' : nat) :=
  (Read val : Bool <- varName;
   Ret (IF Var type (SyntaxKind Bool) val
        then Const type (natToWord size' 0)
        else Const type $ (1)%word))%kami_action.

Local Definition first_impl1 (k : Kind) (bvarName dvarName : string)  :=
(Read val : Bool <- bvarName;
 Read dat : k <- dvarName;
 Ret (STRUCT {"valid" ::= Var type (SyntaxKind Bool) val;
              "data" ::= Var type (SyntaxKind k) dat}:
      Expr type (SyntaxKind (Maybe k))))%kami_action.  

Local Definition deq_impl1 (k : Kind) (bvarName dvarName : string) :=
(Read val : Bool <- bvarName;
 Read dat : k <- dvarName;
 Write bvarName : Bool <- Const type false;
 Ret (STRUCT {"valid" ::= Var type (SyntaxKind Bool) val;
              "data" ::= Var _ (SyntaxKind k) dat}:
        Expr _ (SyntaxKind (Maybe k))))%kami_action.

Local Definition enq_impl1 (k : Kind) (bvarName dvarName : string) (new : type k) :=
  (Read val : Bool <- bvarName;
   Read dat : k <- dvarName;
   Write bvarName : Bool <- Const type true;
   Write dvarName : k <-
                    IF ! Var type (SyntaxKind Bool) val
                    then Var _ (SyntaxKind k) new
                    else Var _ _ dat;
   Ret (! Var _ (SyntaxKind Bool) val))%kami_action.

Local Definition flush_impl1 (varName : string) :=
(Write varName : Bool <- Const type false; Retv)%kami_action.

Local Lemma isEmpty1_Effectless varName val :
  forall o reads upds calls retV,
    NoDup (map fst o) ->
    In (varName, existT _ (SyntaxKind Bool) val) o ->
    SemAction o (isEmpty_impl1 varName) reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    retV = negb val.
Proof.
  unfold isEmpty_impl1; intros.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H2; dest; subst.
  repeat split; auto.
  enough ( x = val).
  { subst; auto. }
  specialize (NoDup_map_fst H H0 H1) as P; EqDep_subst; reflexivity.
Qed.

Local Lemma isEmpty1_Wb varName :
  ActionWb [(varName, SyntaxKind Bool)] (isEmpty_impl1 varName).
Proof.
  unfold isEmpty_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  assert (SubList [(varName, existT (fullType type) (SyntaxKind Bool) x0)] o).
  { repeat intro.
    inv H3; [|inv H4]; assumption. }
  specialize (SubList_chain H H0 H3) as P.
  rewrite <- fst_getKindAttr in P.
  setoid_rewrite H2 in P.
  rewrite (P (eq_refl _)) in *.
  split.
  - exists [(varName, existT _ (SyntaxKind Bool) x0)]; repeat split; auto.
    + apply SubList_refl.
    + repeat econstructor.
  - apply SubList_nil_l.
Qed.

Local Lemma isFull1_Effectless varName val :
  forall o reads upds calls retV,
    NoDup (map fst o) ->
    In (varName, existT _ (SyntaxKind Bool) val) o ->
    SemAction o (isFull_impl1 varName) reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    retV = val.
Proof.
  unfold isFull_impl1; intros.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H2; dest; subst.
  repeat split; auto.
  enough ( x = val).
  { subst; auto. }
  specialize (NoDup_map_fst H H0 H1) as P; EqDep_subst; reflexivity.
Qed.

Local Lemma isFull1_Wb varName :
  ActionWb [(varName, SyntaxKind Bool)] (isFull_impl1 varName).
Proof.
  unfold isFull_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  assert (SubList [(varName, existT (fullType type) (SyntaxKind Bool) x0)] o).
  { repeat intro.
    inv H3; [|inv H4]; assumption. }
  specialize (SubList_chain H H0 H3) as P.
  rewrite <- fst_getKindAttr in P.
  setoid_rewrite H2 in P.
  rewrite (P (eq_refl _)) in *.
  split.
  - exists [(varName, existT _ (SyntaxKind Bool) x0)]; repeat split; auto.
    + apply SubList_refl.
    + repeat econstructor.
  - apply SubList_nil_l.
Qed.

Local Lemma numFree1_Effectless varName size' val :
  forall o reads upds calls retV,
    NoDup (map fst o) ->
    In (varName, existT _ (SyntaxKind Bool) val) o ->
    SemAction o (numFree_impl1 varName size') reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    retV = (if val then (natToWord size' 0) else (natToWord size' 1)).
Proof.
  unfold numFree_impl1; intros.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H2; dest; subst.
  repeat split; auto.
  enough ( x = val).
  { subst; auto. }
  specialize (NoDup_map_fst H H0 H1) as P; EqDep_subst; reflexivity.
Qed.

Local Lemma numFree1_Wb varName size' :
  ActionWb [(varName, SyntaxKind Bool)] (numFree_impl1 varName size').
Proof.
  unfold numFree_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  assert (SubList [(varName, existT (fullType type) (SyntaxKind Bool) x0)] o).
  { repeat intro.
    inv H3; [|inv H4]; assumption. }
  specialize (SubList_chain H H0 H3) as P.
  rewrite <- fst_getKindAttr in P.
  setoid_rewrite H2 in P.
  rewrite (P (eq_refl _)) in *.
  split.
  - exists [(varName, existT _ (SyntaxKind Bool) x0)]; repeat split; auto.
    + apply SubList_refl.
    + repeat econstructor.
  - apply SubList_nil_l.
Qed.

Local Lemma first1_Effectless k bvarName dvarName bval dval:
  forall o reads upds calls retV,
    NoDup (map fst o) ->
    In (bvarName, existT _ (SyntaxKind Bool) bval) o ->
    In (dvarName, existT _ (SyntaxKind k) dval) o ->
    SemAction o (first_impl1 k bvarName dvarName) reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    (retV F1 = bval) /\
    (retV (FS F1) = dval).
Proof.
  unfold first_impl1; intros.
  apply inversionSemAction in H2; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  repeat split; auto.
  - specialize (NoDup_map_fst H H0 H2) as P; EqDep_subst; reflexivity.
  - specialize (NoDup_map_fst H H1 H3) as P; EqDep_subst; reflexivity.
Qed.

Local Lemma first1_Wb k bvarName dvarName :
  ActionWb [(bvarName, SyntaxKind Bool); (dvarName, SyntaxKind k)]
           (first_impl1 k bvarName dvarName).
Proof.
  unfold first_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  split; [|apply SubList_nil_l].
  exists x.
  assert (SubList [(bvarName, existT _ (SyntaxKind Bool) x0);
                   (dvarName, existT _ (SyntaxKind k) x2)] o).
  { repeat intro.
    inv H4; [|inv H5; [|inv H4]]; assumption. }
  specialize (SubList_chain H H0 H4) as P.
  rewrite <- fst_getKindAttr in P.
  setoid_rewrite H2 in P.
  rewrite (P (eq_refl _)) in *.
  repeat split; auto.
  - apply SubList_refl.
  - econstructor; eauto.
    + left; reflexivity.
    + econstructor; eauto.
      * right; left; reflexivity.
      * econstructor; eauto.
Qed.

Local Lemma deq1_Effectful k bvarName dvarName bval dval :
  forall o reads upds calls retV,
    NoDup (map fst o) ->
    In (bvarName, existT _ (SyntaxKind Bool) bval) o ->
    In (dvarName, existT _ (SyntaxKind k) dval) o ->
    SemAction o (deq_impl1 k bvarName dvarName) reads upds calls retV ->
    upds = [(bvarName, existT _ (SyntaxKind Bool) false)] /\
    calls = nil /\
    (retV F1 = bval) /\
    (retV (FS F1) = dval).
Proof.
  unfold deq_impl1; intros.
  apply inversionSemAction in H2; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  apply inversionSemAction in H6; dest; subst.
  repeat split; auto.
  - specialize (NoDup_map_fst H H0 H2) as P; EqDep_subst; reflexivity.
  - specialize (NoDup_map_fst H H1 H3) as P; EqDep_subst; reflexivity.
Qed.

Local Lemma deq1_Wb k bvarName dvarName :
  ActionWb [(bvarName, SyntaxKind Bool); (dvarName, SyntaxKind k)]
           (deq_impl1 k bvarName dvarName).
Proof.
  unfold deq_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  apply inversionSemAction in H6; dest; subst.
  split.
  - exists x.
    assert (SubList [(bvarName, existT _ (SyntaxKind Bool) x0);
                     (dvarName, existT _ (SyntaxKind k) x2)] o).
    { repeat intro.
      inv H6; [|inv H7; [|inv H6]]; assumption. }
  specialize (SubList_chain H H0 H6) as P.
  rewrite <- fst_getKindAttr in P.
  setoid_rewrite H2 in P.
  rewrite (P (eq_refl _)) in *.
  repeat split; auto.
    + apply SubList_refl.
    + econstructor; eauto.
      * left; reflexivity.
      * econstructor; eauto.
        -- right; left; reflexivity.
        -- econstructor; eauto.
           ++ left; auto.
           ++ econstructor; eauto.
  - repeat intro; inv H6;[|inv H7].
    left; reflexivity.
Qed.

Local Lemma eqn1_Effectful k bvarName dvarName bval dval new:
  forall o reads upds calls retV,
    NoDup (map fst o) ->
    In (bvarName, existT _ (SyntaxKind Bool) bval) o ->
    In (dvarName, existT _ (SyntaxKind k) dval) o ->
    SemAction o (enq_impl1 k bvarName dvarName new) reads upds calls retV ->
    upds = [(bvarName, existT _ (SyntaxKind Bool) true);
           (dvarName, existT _ (SyntaxKind k) 
                             (if (negb bval)
                             then new
                             else dval))] /\
    calls = nil /\
    (retV = negb bval).
Proof.
  unfold enq_impl1; intros.
  apply inversionSemAction in H2; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  apply inversionSemAction in H6; dest; subst.
  apply inversionSemAction in H8; dest; subst.
  specialize (NoDup_map_fst H H0 H2) as P; EqDep_subst;
    specialize (NoDup_map_fst H H1 H3) as P1; EqDep_subst.
  repeat split; auto.
Qed.

Local Lemma eqn1_Wb k bvarName dvarName new:
  ActionWb [(bvarName, SyntaxKind Bool); (dvarName, SyntaxKind k)]
           (enq_impl1 k bvarName dvarName new).
Proof.
  unfold enq_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H3; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  apply inversionSemAction in H6; dest; subst.
  apply inversionSemAction in H8; dest; subst.
  split.
  - exists x.
    assert (SubList [(bvarName, existT _ (SyntaxKind Bool) x0);
                     (dvarName, existT _ (SyntaxKind k) x2)] o).
    { repeat intro.
      inv H8; [|inv H9; [|inv H8]]; assumption. }
  specialize (SubList_chain H H0 H8) as P.
  rewrite <- fst_getKindAttr in P.
  setoid_rewrite H2 in P.
  rewrite (P (eq_refl _)) in *.
  repeat split; auto.
    + apply SubList_refl.
    + econstructor; eauto.
      * left; reflexivity.
      * econstructor; eauto.
        -- right; left; reflexivity.
        -- econstructor; eauto.
           ++ left; auto.
           ++ econstructor; eauto.
              ** right; left; reflexivity.
              ** econstructor; reflexivity.
  - repeat intro; inv H8;[|inv H9; [|inv H8]].
    + left; reflexivity.
    + right; left; reflexivity.
Qed.

Local Lemma flush1_Effectful varName :
  forall o reads upds calls retV,
    SemAction o (flush_impl1 varName) reads upds calls retV ->
    upds = [(varName, existT _ (SyntaxKind Bool) false)] /\
    calls = nil /\
    (retV = WO).
Proof.
  unfold flush_impl1; intros.
  apply inversionSemAction in H; dest; subst.
  apply inversionSemAction in H1; dest; subst.
  repeat split; auto.
Qed.

Local Lemma flush_Wb varName:
  ActionWb [(varName, SyntaxKind Bool)]
           (flush_impl1 varName).
Proof.
  unfold flush_impl1.
  repeat intro.
  rewrite SubList_map_iff in H0; dest.
  apply inversionSemAction in H1; dest; subst.
  apply inversionSemAction in H4; dest; subst.
  split; [|apply SubList_refl].
  exists x.
  repeat split; auto.
  - apply SubList_nil_l.
  - repeat econstructor; eauto.
    rewrite H2.
    left; reflexivity.
Qed.

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
    firstCorrect : EffectlessRelation fifoR (@first _ imp type) (@first _ spec type);
    firstWb : ActionWb fifoRegs (@first _ imp type);
    deqCorrect : EffectfulRelation fifoR (@deq _ imp type) (@deq _ spec type);
    deqWb : ActionWb fifoRegs (@deq _ imp type);
    enqCorrect : forall val, EffectfulRelation fifoR (@enq _ imp type val) (@enq _ spec type val);
    enqWb : forall val, ActionWb fifoRegs (@enq _ imp type val);
    flushCorrect : EffectfulRelation fifoR (@flush _ imp type) (@flush _ spec type);
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
