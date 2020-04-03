Require Import Coq.Logic.EqdepFacts.
Require Import Kami.All.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import Kami.GallinaModules.Relations.
Require Import StdLibKami.RegArray.Impl.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.Spec.
Require Import StdLibKami.RegArray.CorrectDef.

Definition SemAction_le {k} (a1 a2 : ActionT type k) :=
  forall o reads upds calls retV,
    SemAction o a2 reads upds calls retV -> SemAction o a1 reads upds calls retV.

Lemma gatherActions_replace_list k_in (l1 l2 : list (ActionT type k_in)):
    Forall2 SemAction_le l1 l2 ->
  forall o reads upds calls k_out retV
         (cont : list (Expr type (SyntaxKind k_in)) -> ActionT type k_out),
    SemAction o (gatherActions l2 cont) reads upds calls retV ->
    SemAction o (gatherActions l1 cont) reads upds calls retV.
Proof.
  induction 1; simpl; auto; intros.
  apply inversionSemAction in H1; dest; subst.
  econstructor; eauto.
Qed.

Local Definition SemAction_Effectless {k} o (a : ActionT type k)
      (e : Expr type (SyntaxKind k)) :=
  forall reads upds calls retV,
    SemAction o a reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    retV = (evalExpr e).

Local Definition SemAction_Effectful {k} o (a : ActionT type k)
      (uces : RegsT * (MethsT * Expr type (SyntaxKind k))):=
  forall reads upds' calls' retV,
    SemAction o a reads upds' calls' retV ->
    upds' = (fst uces) /\
    calls' = (fst (snd uces)) /\
    retV = evalExpr (snd (snd uces)).

Lemma SemReturn':
  forall k (e1 e2 : Expr type (SyntaxKind k)),
    evalExpr e1 = evalExpr e2 ->
    forall o reads upds calls retV,
      SemAction o (Return e1) reads upds calls retV <->
      SemAction o (Return e2) reads upds calls retV.
Proof.
  red; split; intros; apply inversionSemAction in H0; dest; subst; econstructor; eauto.
Qed.
  
Lemma gatherActions_effectless k_in (acts : list (ActionT type k_in)) :
  forall (exprs : list (Expr type (SyntaxKind k_in))) k_out
         (f : list (Expr type (SyntaxKind k_in)) -> Expr type (SyntaxKind k_out))
         o1 o2 reads upds calls retV,
    Forall2 (SemAction_Effectless o1) acts exprs ->
    (forall exprs exprs', Forall2 (fun x y => evalExpr x = evalExpr y) exprs exprs' ->
                    evalExpr (f exprs) = evalExpr (f exprs')) ->
    SemAction o1 (gatherActions acts (fun exprs => Return (f exprs))) reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    SemAction o2 (Return (f exprs)) nil nil nil retV.
Proof.
  induction acts; intros; inv H; simpl in *.
  - apply inversionSemAction in H1; dest; subst.
    repeat split; auto.
    econstructor; auto.
  - apply inversionSemAction in H1; dest; subst.
    specialize (H4 _ _ _ _ H1); dest; subst.
    assert (forall exprs exprs',
               Forall2 (fun x y => evalExpr x = evalExpr y) exprs
                       exprs' ->
               evalExpr ((fun l => f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l)) exprs) =
               evalExpr ((fun l => f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l)) exprs')) as P.
    { intros; apply H0.
      constructor; auto. }
    specialize (IHacts l' k_out (fun l => f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l))
                       _ o2 _ _  _ _ H6 P H2); dest; subst.
    repeat split; auto.
    rewrite (SemReturn' _ (f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l'))); [assumption|].
    apply H0.
    constructor; simpl; auto.
    clear; induction l'; simpl; auto.
Qed.

Lemma gatherActions_effectful k_in (acts : list (ActionT type k_in)) :
  forall k_out (f : list (Expr type (SyntaxKind k_in)) -> Expr type (SyntaxKind k_out))
         o1 reads upds calls retV luce,
    Forall2 (SemAction_Effectful o1) acts luce ->
    (forall exprs exprs', Forall2 (fun x y => evalExpr x = evalExpr y) exprs exprs' ->
                    evalExpr (f exprs) = evalExpr (f exprs')) ->
    SemAction o1 (gatherActions acts (fun exprs => Return (f exprs))) reads upds calls retV ->
    upds = concat (map fst luce) /\
    calls = concat (map (fun x => fst (snd x)) luce) /\
    retV = evalExpr (f (map (fun x => (snd (snd x))) luce)).
Proof.
  induction acts; intros; inv H; simpl in *.
  - apply inversionSemAction in H1; dest; subst.
    repeat split; auto.
  - apply inversionSemAction in H1; dest; subst.
    specialize (H4 _ _ _ _ H1); destruct y, p; dest; simpl in *; subst.
    assert (forall exprs exprs',
               Forall2 (fun x y => evalExpr x = evalExpr y) exprs
                       exprs' ->
               evalExpr ((fun l => f ((Var _ (SyntaxKind k_in) (evalExpr e)) :: l)) exprs) =
               evalExpr ((fun l => f ((Var _ (SyntaxKind k_in) (evalExpr e)) :: l)) exprs')) as P.
    { intros; apply H0.
      constructor; auto. }
    specialize (IHacts k_out (fun l => f ((Var _ (SyntaxKind k_in) (evalExpr e)) :: l))
                       _ _ _  _ _ l' H6 P H2); dest; subst.
    repeat split; auto.
    apply H0; constructor; simpl; auto.
    clear.
    induction l'; constructor; auto.
Qed.

Lemma gatherActions_effectless' k_in (acts : list (ActionT type k_in)) :
  forall (exprs : list (Expr type (SyntaxKind k_in))) k_out
         (f : list (Expr type (SyntaxKind k_in)) -> ActionT type k_out)
         o1 o2 reads upds calls retV,
    Forall2 (SemAction_Effectless o1) acts exprs ->
    (forall exprs exprs', Forall2 (fun x y => evalExpr x = evalExpr y) exprs exprs' ->
                          (forall o1 o2 reads upds calls retV,
                              SemAction o1 (f exprs) reads upds calls retV ->
                              upds = nil /\
                              calls = nil /\
                              exists reads,
                                SemAction o2 (f exprs') reads upds calls retV)) ->
    SemAction o1 (gatherActions acts f) reads upds calls retV ->
    upds = nil /\
    calls = nil /\
    exists reads',
      SemAction o2 (f exprs) reads' upds calls retV.
Proof.
  induction acts; intros; inv H; simpl in *.
  - specialize (H0 nil nil (Forall2_nil _) _ o2 _ _ _ _ H1); dest; subst.
    repeat split; auto.
    exists x; assumption.
  - apply inversionSemAction in H1; dest; subst.
    specialize (H4 _ _ _ _ H1); dest; subst.
    assert (forall exprs exprs',
               Forall2 (fun x y => evalExpr x = evalExpr y) exprs exprs' ->
               forall (o1 o2 reads upds : RegsT) (calls : MethsT) (retV : type k_out),
                 SemAction o1 ((fun l => f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l)) exprs)
                                reads upds calls retV ->
                 upds = [] /\
                 calls = [] /\
                 (exists reads, SemAction o2
                       ((fun l => f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l)) exprs')
                       reads upds calls retV)) as P.
    { intros; simpl.
      eapply H0; eauto. }
    specialize (IHacts l' k_out (fun l => f ((Var _ (SyntaxKind k_in) (evalExpr y)) :: l))
                       _ o2 _ _  _ _ H6 P H2); dest; simpl.
    eapply (H0 (Var type (SyntaxKind k_in) (evalExpr y) :: l') (y :: l')); eauto.
    constructor; auto.
    clear; induction l'; auto.
Qed.

Local Definition impl_read k size size' idx (f : nat -> string) :=
  (GatherActions map
                 (fun '(i, reg) =>
                  Read val : k <- reg;
                  Ret (IF Const type $ (i)%word ==
                          Var type (SyntaxKind (Bit (Nat.log2_up size'))) idx
                       then Var type (SyntaxKind k) val
                       else Const type Default))
                 (tag (map f (seq O size))) as vals;
  Ret (Kor vals))%kami_action.

Local Definition impl_write k size size' (writeRq : type (WriteRq (Nat.log2_up size') k))
      (f : nat -> string) :=
  (GatherActions map
                 (fun '(i, reg) =>
                  Read val : k <- reg;
                  Write reg : k <-
                  IF Const type $ (i)%word ==
                     ReadStruct (Var _ (SyntaxKind (WriteRq (Nat.log2_up size') k)) writeRq) F1
                  then ReadStruct (Var _ (SyntaxKind (WriteRq (Nat.log2_up size') k)) writeRq)
                                  (FS F1)
                  else Var type _ val; Retv)
                 (tag (map f (seq O size))) as vals; Retv)%kami_action.

Lemma MaybeReadevalCorrect k :
  forall (x y : Expr type (SyntaxKind (Maybe k))) (i : t 2),
         evalExpr x = evalExpr y ->
         evalExpr (ReadStruct x i) = evalExpr (ReadStruct y i).
Proof.
  simpl; intros.
  unfold Maybe, getStruct in *; simpl in *.
  rewrite H.
  reflexivity.
Qed.

Definition sparseList {A : Type} (def : A) (l : list A) (n size : nat) :=
  map (fun x => if Nat.eqb x n then nth_default def l n else def) (seq 0 size).

Definition sparseList' {A: Type} (def : A) (l : list A) (n : nat) :=
  sparseList def l n (length l).

Definition replace_nth {A : Type} (l : list A) (n : nat) (val : A) :=
  firstn n l ++ (match hd_error (skipn n l) with
                 | None => nil
                 | Some a => [val]
                 end) ++ tl (skipn n l).

Definition defList {A : Type} (def : A) size :=
  map (fun _ => def) (seq 0 size).

Definition defList' {A : Type} (def : A) (l : list A) :=
  map (fun _ => def) (seq 0 (length l)).

Lemma sparse_eq {A : Type} (def : A) (l : list A) :
  forall n size,
    n < size ->
    nth_error (sparseList def l n size) n = Some (nth_default def l n).
Proof.
  intros.
  unfold sparseList, nth_default.
  destruct (nth_error l _) eqn:G.
  - induction size; [lia|].
    apply lt_n_Sm_le in H.
    destruct (le_lt_or_eq _ _ H).
    + rewrite seq_eq, map_app, nth_error_app1.
      * apply IHsize; assumption.
      * rewrite map_length, seq_length; assumption.
    + rewrite seq_eq, map_app, nth_error_app2.
      * rewrite map_length, seq_length, plus_O_n, H0, diag; simpl.
        rewrite Nat.eqb_refl; reflexivity.
      * rewrite map_length, seq_length; lia.
  - induction size; [lia|].
    apply lt_n_Sm_le in H.
    destruct (le_lt_or_eq _ _ H).
    + rewrite seq_eq, map_app, nth_error_app1.
      * apply IHsize; assumption.
      * rewrite map_length, seq_length; assumption.
    + rewrite seq_eq, map_app, nth_error_app2.
      * rewrite map_length, seq_length, plus_O_n, H0, diag; simpl.
        rewrite Nat.eqb_refl; reflexivity.
      * rewrite map_length, seq_length; lia.
Qed.
      
Lemma sparse_size_le {A : Type} (l : list A):
  forall def n size,
    size <= n ->
    (forall a,
        In a (sparseList def l n size)-> a = def).
Proof.
  induction size; intros; [contradiction|].
  unfold sparseList in H0.
  rewrite seq_eq, map_app, in_app_iff in H0.
  destruct H0.
  - apply IHsize; [lia|assumption].
  - rewrite in_map_iff in H0; dest.
    simpl in H1; destruct H1; [|contradiction]; subst.
    destruct Nat.eqb eqn:G; auto.
    exfalso.
    rewrite Nat.eqb_eq in G; subst.
    lia.
Qed.

Lemma sparse_neq {A : Type} (def : A) (l : list A) :
  forall n m size,
    n < size ->
    m < size ->
    m <> n ->
    nth_error (sparseList def l n size) m = Some def.
Proof.
  induction size; intros; [lia|].
  unfold sparseList.
  rewrite seq_eq, map_app.
  apply lt_n_Sm_le in H; apply lt_n_Sm_le in H0.
  destruct (le_lt_or_eq _ _ H), (le_lt_or_eq _ _ H0).
  - rewrite nth_error_app1.
    + apply IHsize; auto.
    + rewrite map_length, seq_length; assumption.
  - rewrite nth_error_app2.
    + rewrite map_length, seq_length, H3, diag; simpl.
      destruct Nat.eqb eqn:G; auto.
      exfalso.
      rewrite Nat.eqb_eq in G.
      apply H1; rewrite H3; assumption.
    + rewrite map_length, seq_length; lia.
  - rewrite nth_error_app1.
    specialize (sparse_size_le l def (Nat.le_refl size)) as P.
    + apply nth_error_map_Some2.
      exists m.
      rewrite <- seq_nth_error_Some.
      destruct Nat.eqb eqn:G; auto.
      exfalso.
      rewrite Nat.eqb_eq in G; lia.
    + rewrite map_length, seq_length; assumption.
  - exfalso.
    apply H1; rewrite H2; assumption.
Qed.

Lemma length_sparseList {A : Type} (def : A) (l : list A) (n size : nat) :
  length (sparseList def l n size) = size.
Proof.
  unfold sparseList.
  rewrite map_length, seq_length; reflexivity.
Qed.

Lemma nth_default_map {A B : Type} (f : A -> B) l def n :
  f (nth_default def l n) = nth_default (f def) (map f l) n.
Proof.
  unfold nth_default.
  destruct nth_error eqn:G.
  - apply (map_nth_error f) in G; rewrite G; reflexivity.
  - rewrite (nth_error_map_None_iff f) in G; rewrite G; reflexivity.
Qed.

Lemma sparseList_map {A B : Type} (f : A -> B) l def :
  forall m size,
    map f (sparseList def l m size) = sparseList (f def) (map f l) m size.
Proof.
  induction size; unfold sparseList in *; auto.
  rewrite seq_eq; repeat rewrite map_app; rewrite IHsize.
  f_equal; cbn [map].
  destruct Nat.eqb; auto.
  rewrite <- nth_default_map; reflexivity.
Qed.

Lemma sparseList_app1 {A : Type} (def : A) :
  forall l1 l2 m size,
    length (l1 ++ l2) <= size ->
    m < length l1 ->
    sparseList def (l1 ++ l2) m size = sparseList' def l1 m ++ defList def (size - length l1).
Proof.
  intros.
  unfold sparseList', sparseList, nth_default, defList.
  rewrite nth_error_app1; auto.
  rewrite <- (le_plus_minus_r (length l1) size) at 1.
  - rewrite seq_app, map_app.
    f_equal; simpl.
    rewrite <- (diag (length l1)), <- Reduce_seq, map_map; auto.
    apply map_ext_in; intros.
    rewrite in_seq in H1.
    destruct Nat.eqb eqn:G; auto.
    exfalso.
    rewrite Nat.eqb_eq in G; subst; lia.
  - rewrite app_length in H; lia.
Qed.

Lemma sparseList_app2 {A : Type} (def : A) :
  forall l1 l2 m size,
    length (l1 ++ l2) <= size ->
    length l1 <= m ->
    sparseList def (l1 ++ l2) m size = defList' def l1 ++
                                                sparseList def l2 (m - length l1)
                                                (size - length l1).
Proof.
  intros.
  unfold sparseList, nth_default, defList'.
  rewrite <- nth_error_app2; auto.
  rewrite <- (le_plus_minus_r (length l1) size) at 1.
  - rewrite seq_app, map_app.
    f_equal.
    + apply map_ext_in; intros.
      rewrite in_seq in H1.
      destruct Nat.eqb eqn:G; auto.
      exfalso.
      rewrite Nat.eqb_eq in G; subst.
      lia.
    + simpl.
      rewrite <- (diag (length l1)), <- Reduce_seq, map_map; auto.
      apply map_ext_in; intros.
      rewrite in_seq in H1.
      destruct Nat.eqb eqn:G.
      * rewrite Nat.eqb_eq in G; subst.
        rewrite Nat.eqb_refl; reflexivity.
      * rewrite Nat.eqb_neq in G.
        destruct Nat.eqb eqn:G0; auto.
        exfalso.
        rewrite Nat.eqb_eq in G0.
        apply G.
        lia.
  - rewrite app_length in H; lia.
Qed.

Lemma sparseList'_app1 {A : Type} (def : A) :
  forall l1 l2 m,
    m < length l1 ->
    sparseList' def (l1 ++ l2) m = sparseList' def l1 m ++ defList' def l2.
Proof.
  intros.
  specialize (@sparseList_app1 _ def l1 l2 m (length (l1 ++ l2)) ltac:(auto) ltac:(auto)) as P.
  unfold sparseList', defList', defList in *.
  rewrite app_length, minus_plus in *.
  assumption.
Qed.

Lemma sparseList'_app2 {A : Type} (def : A) :
  forall l1 l2 m,
    length l1 <= m ->
    sparseList' def (l1 ++ l2) m = defList' def l1 ++ sparseList' def l2 (m - length l1).
Proof.
  intros.
  specialize (@sparseList_app2 _ def l1 l2 m (length (l1 ++ l2)) ltac:(auto) ltac:(auto)) as P.
  unfold sparseList', defList' in *.
  rewrite app_length, minus_plus in *.
  assumption.
Qed.

Lemma evalExpr_Kor_sparseList (k : Kind) l :
  forall size m (len_size : length l = size),
    evalExpr
      (Kor
         (sparseList (Var _ _ (evalExpr (Const type Default)))
                     (map (fun x => Var _ _ x) l)
                     m size)) =
    nth_default (evalExpr (@Const type k Default)) l m.
Proof.
  intros.
  rewrite <- sparseList_map.
  destruct (le_lt_dec size m).
  - unfold nth_default.
    specialize (sparse_size_le l (evalExpr (Const type Default)) l0) as P.
    rewrite <- len_size, <- nth_error_None in l0.
    rewrite l0.
    destruct size.
    + simpl; reflexivity.
    + apply Kor_sparse.
      * rewrite map_map.
        cbn [evalExpr].
        rewrite map_id.
        destruct (sparseList _ _ _ _) eqn:G.
        -- exfalso.
           apply <- length_zero_iff_nil in G.
           rewrite length_sparseList in G; discriminate.
        -- rewrite (P _ (in_eq _ _)); left; reflexivity.
      * intros.
        rewrite map_map in H.
        cbn [evalExpr] in H.
        rewrite map_id in H.
        auto.
  - unfold sparseList.
    unfold nth_default; destruct nth_error eqn:G.
    + rewrite map_map.
      assert (forall x, x = (evalExpr (Var _ (SyntaxKind k) x))) as P by reflexivity.
      rewrite (P f) at 1.
      apply Kor_sparse; rewrite map_map.
      * rewrite in_map_iff.
        exists m.
        rewrite Nat.eqb_refl; split; auto.
        rewrite in_seq; lia.
      * intros.
        rewrite in_map_iff in H; dest.
        destruct Nat.eqb; auto.
    + rewrite nth_error_None in G; lia.
Qed.

Lemma sparseList_def {A : Type} (def : A) l m size :
  length l <= m ->
  sparseList def l m size = defList def size.
Proof.
  intros.
  unfold sparseList, defList.
  apply map_ext_in; intros.
  rewrite in_seq in H0.
  destruct Nat.eqb; auto.
  unfold nth_default.
  destruct nth_error eqn:G; auto.
  exfalso.
  assert (nth_error l m <> None) as P.
  { intro P; rewrite P in G; discriminate. }
  rewrite nth_error_Some in P.
  lia.
Qed.

Lemma sparseList_def2 {A : Type} (def : A) l m size :
  size <= m ->
  sparseList def l m size = defList def size.
Proof.
  intros.
  induction size.
  - unfold sparseList, defList; simpl; reflexivity.
  - unfold sparseList, defList in *.
    rewrite seq_eq.
    repeat rewrite map_app.
    rewrite IHsize; try lia.
    f_equal; simpl.
    destruct Nat.eqb eqn:G; auto.
    exfalso.
    rewrite Nat.eqb_eq in G; subst; lia.
Qed.

Lemma sparseList'_def {A : Type} (def : A) l m :
  length l <= m ->
  sparseList' def l m = defList' def l.
Proof.
  intros.
  unfold sparseList', defList'.
  apply sparseList_def; assumption.
Qed.

Definition valsToRegs k (f : nat -> string) (l : list (type k)) :=
  map (fun x => (f x, existT (fullType type) (SyntaxKind k)
                             (nth_default (evalConstT Default)
                                          l x))) (seq 0 (length l)).

Local Lemma defList_helper k :
  forall o size size' (idx : word (Nat.log2_up size')) (f : nat -> string)
         (Hsize : size <= size') (idxBound : size <= wordToNat idx),
    Forall2 (SemAction_Effectless o)
            (map
               (fun '(i, reg) =>
                  (Read val : k <- reg;
                  Ret (IF Const type $ (i)%word ==
                       Var type (SyntaxKind
                                   (Bit (Nat.log2_up size'))) idx
                       then Var _ (SyntaxKind k) val
                       else Const _ Default))%kami_action)
               (tag (map f (seq 0 size))))
            (defList (Var type (SyntaxKind k) (evalExpr (Const type Default)))
                     size).
Proof.
  intros.
  induction size; unfold defList.
  - constructor.
  - unfold tag in *.
    rewrite seq_eq, map_app, tagApp; repeat rewrite map_app.
    apply Forall2_app.
    + apply IHsize; lia.
    + constructor;[|constructor].
      repeat intro.
      apply inversionSemAction in H; dest; subst.
      apply inversionSemAction in H0; dest; subst.
      repeat split; auto.
      simpl.
      destruct weq; simpl; auto.
      exfalso.
      rewrite map_length, seq_length, Nat.add_0_r in e.
      assert (wordToNat (natToWord (Nat.log2_up size') (size)) = wordToNat idx) as P.
      { rewrite e; reflexivity. }
      rewrite (wordToNat_natToWord_eqn _ size), Nat.mod_small in P; [lia|].
      apply (Nat.lt_le_trans _ size'); [lia|].
      apply log2_up_pow2.
Qed.

Lemma impl_read_reduction k (l : list (type k)):
  forall (f : nat -> string) (idx : word (Nat.log2_up (length l))),
    (forall n m, f n = f m -> n = m) ->
    forall reads upds calls retV,
      SemAction (valsToRegs k f (rev l))
                (impl_read k (length l) (length l) idx f) reads upds calls retV ->
      upds = nil /\ calls = nil /\ retV = nth_default (evalExpr (Const type Default))
                                                      (rev l) (wordToNat idx).
Proof.
  unfold impl_read; intros.
  eapply gatherActions_effectless with (o2 := nil) (exprs :=
                                                    sparseList'
                                                    (Var _ _ (evalExpr (Const type Default)))
                                                    (map (fun x => Var _ (SyntaxKind k) x)
                                                         (rev l))
                                                      (wordToNat idx)) in H0;
    dest; repeat split; eauto.
  - apply inversionSemAction in H2; dest; subst.
    apply evalExpr_Kor_sparseList.
    apply eq_sym, map_length.
  - clear H0.
    destruct (le_lt_dec (length (rev l)) (wordToNat idx)).
    + rewrite sparseList'_def; [|rewrite map_length; assumption].
      unfold defList'.
      rewrite map_length, rev_length in *.
      apply defList_helper; auto.
    + enough (forall size size' (idx : word (Nat.log2_up size'))
                     (Hsize : size <= size')
                     (HlenSz : size <= length l)
                     (idxBound : wordToNat idx < size),
                 Forall2 (SemAction_Effectless (valsToRegs k f (rev l)))
                         (map
                            (fun '(i, reg) =>
                               (Read val : k <- reg;
                                Ret (IF Const type $ (i)%word ==
                                     Var type (SyntaxKind
                                                 (Bit (Nat.log2_up size'))) idx
                                     then Var _ (SyntaxKind k) val
                                     else Const _ Default))%kami_action)
                            (tag (map f (seq 0 size))))
                         (sparseList (Var type (SyntaxKind k) (evalExpr (Const type Default)))
                                     (map (fun x => Var _ (SyntaxKind k) x) (rev l))
                                     (wordToNat idx) size)) as P0.
      { unfold sparseList'.
        rewrite map_length, rev_length in *.
        apply P0; auto.
      }
      clear - H.
      intros.
      induction size.
      * constructor.
      * unfold tag in *.
        rewrite Nat.lt_succ_r in idxBound.
        apply le_lt_or_eq in idxBound.
        destruct idxBound.
        -- unfold sparseList in *.
          rewrite seq_eq, map_app, tagApp; repeat rewrite map_app.
          apply Forall2_app.
           ++ apply IHsize; auto; try lia.
           ++ constructor;[|constructor].
              repeat intro.
              apply inversionSemAction in H1; dest; subst.
              apply inversionSemAction in H2; dest; subst.
              repeat split; auto.
              simpl.
              destruct weq; simpl; rewrite map_length, seq_length, Nat.add_0_r in *.
              ** destruct Nat.eqb eqn:G.
                 --- rewrite nth_default_map, map_map, map_id; simpl in *.
                     unfold valsToRegs in H1.
                     rewrite in_map_iff in H1; dest.
                     apply inversionPair in H1; dest.
                     apply H in H1.
                     rewrite Nat.eqb_eq in G.
                     EqDep_subst.
                     rewrite wordToNat_natToWord_eqn, Nat.mod_small; auto.
                     apply (Nat.lt_le_trans _ size'); lia.
                 --- exfalso.
                     rewrite Nat.eqb_neq in G.
                     apply G.
                     assert (wordToNat (natToWord (Nat.log2_up size') size) =
                             wordToNat idx) as P.
                     { rewrite e; reflexivity. }
                     rewrite wordToNat_natToWord_eqn, Nat.mod_small in P; auto.
                     apply (Nat.lt_le_trans _ size'); try lia.
                     apply log2_up_pow2.
              ** destruct Nat.eqb eqn:G.
                 --- exfalso.
                     rewrite Nat.eqb_eq in G.
                     rewrite G, natToWord_wordToNat in n; contradiction.
                 --- reflexivity.
        -- clear IHsize.
           rewrite Nat.le_succ_l in *.
           rewrite <- sparseList_map.
           unfold sparseList.
           rewrite seq_eq, map_app, tagApp; repeat rewrite map_app.
           apply Forall2_app.
           ++ fold (sparseList (evalExpr (@Const type k Default)) (rev l)
                               (wordToNat idx) size).
              subst.
              rewrite sparseList_map.
              rewrite sparseList_def2; auto.
              apply defList_helper; auto; try lia.
           ++ rewrite map_map; constructor; [|constructor].
              repeat intro.
              apply inversionSemAction in H1; dest; subst.
              apply inversionSemAction in H2; dest; subst.
              repeat split; auto.
              simpl.
              destruct weq; simpl; rewrite map_length, seq_length, Nat.add_0_r in *.
              ** destruct Nat.eqb eqn:G.
                 --- unfold valsToRegs in H1.
                     rewrite in_map_iff in H1; dest.
                     apply inversionPair in H0; dest.
                     apply H in H0.
                     EqDep_subst; simpl; reflexivity.
                 --- exfalso.
                     rewrite Nat.eqb_neq in G.
                     contradiction.
  ** exfalso.
     apply n.
     rewrite natToWord_wordToNat; reflexivity.
  - clear.
    induction 1; auto.
    repeat rewrite evalExpr_Kor_head.
    rewrite H, IHForall2; reflexivity.
Qed.

Lemma of_pos_inj1 :
  forall s1 s2,
  (forall m, of_pos m s1 = of_pos m s2) ->
  s1 = s2.
Proof.
  intros s1; elim s1; simpl; intros s2; case s2; auto.
  - intros.
    specialize (H 1%positive); simpl in H.
    discriminate.
  - intros; simpl in *.
    specialize (H0 1%positive); simpl in H0.
    rewrite (append_cons "1" _), (append_cons _ s0) in H0.
    rewrite append_remove_prefix in H0.
    assumption.
Qed.

Lemma natToHexStr_inj :
  forall n m,
    natToHexStr n = natToHexStr m ->
    n = m.
Proof.
Admitted.

Fixpoint hexStrToNat' (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String a s' => match a with
                   | "0"%char => (hexStrToNat' s' (16 * acc + 0))
                   | "1"%char => (hexStrToNat' s' (16 * acc + 1))
                   | "2"%char => (hexStrToNat' s' (16 * acc + 2))
                   | "3"%char => (hexStrToNat' s' (16 * acc + 3))
                   | "4"%char => (hexStrToNat' s' (16 * acc + 4))
                   | "5"%char => (hexStrToNat' s' (16 * acc + 5))
                   | "6"%char => (hexStrToNat' s' (16 * acc + 6))
                   | "7"%char => (hexStrToNat' s' (16 * acc + 7))
                   | "8"%char => (hexStrToNat' s' (16 * acc + 8))
                   | "9"%char => (hexStrToNat' s' (16 * acc + 9))
                   | "A"%char => (hexStrToNat' s' (16 * acc + 10))
                   | "B"%char => (hexStrToNat' s' (16 * acc + 11))
                   | "C"%char => (hexStrToNat' s' (16 * acc + 12))
                   | "D"%char => (hexStrToNat' s' (16 * acc + 13))
                   | "E"%char => (hexStrToNat' s' (16 * acc + 14))
                   | "F"%char => (hexStrToNat' s' (16 * acc + 15))
                   | _ => 0
                   end
  end.

Definition hexStrToNat (s : string) := hexStrToNat' s 0.

Lemma decomposeGatherActions k_in (acts : list (ActionT type k_in)) :
  forall k_out (cont : list (Expr type (SyntaxKind k_in)) -> ActionT type k_out),
  forall o reads upds calls ret,
    SemAction o (GatherActions acts as vals; cont vals)%kami_action reads upds calls ret ->
    exists (fl : list (RegsT * (RegsT * (MethsT * (type k_in))))) reads' upds' calls',
      NoDup (map fst (concat (map (fun x => fst (snd x)) fl))) /\
      DisjKey (concat (map (fun x => fst (snd x)) fl)) upds' /\ 
      reads = concat (map (fun x => fst x) fl) ++ reads' /\
      upds = concat (map (fun x => fst (snd x)) fl) ++ upds' /\
      calls = concat (map (fun x => fst (snd (snd x))) fl) ++ calls' /\
      Forall2 (fun a f => SemAction o a (fst f) (fst (snd f))
                                    (fst (snd (snd f))) (snd (snd (snd f)))) acts fl /\
      SemAction o (cont (map (fun x =>
                                Var type (SyntaxKind k_in) (snd (snd (snd x)))) fl))
                reads' upds' calls' ret.
Proof.
  induction acts; intros.
  - exists nil, reads, upds, calls; simpl.
    repeat split; auto.
    + constructor.
    + apply DisjKey_nil_l.
  - simpl in H.
    apply inversionSemAction in H; dest; subst.
    specialize (IHacts _ _ _ _ _ _ _ H1); dest; subst.
    exists ((x, (x0, (x1, x5)))::x6), x7, x8, x9; simpl; repeat split
    ; try rewrite app_assoc; auto; rewrite DisjKey_app_split_r in H; dest.
    + rewrite NoDup_app_DisjKey; repeat split; auto.
      * apply (SemAction_NoDup_u H0).
    + rewrite DisjKey_app_split_l; split; auto.
Qed.

Lemma gatherActionsWb_contWb k_in (acts : list (ActionT type k_in))
      k_out (cont : list (Expr type (SyntaxKind k_in)) -> ActionT type k_out) myRegs :
  (forall exprs, ActionWb myRegs (cont exprs)) ->
  (forall a,
      In a acts ->
      ActionWb myRegs a) ->
  forall (f : list (Expr type (SyntaxKind k_in)) -> list (Expr type (SyntaxKind k_in))),
    ActionWb myRegs (GatherActions acts as vals; cont (f vals))%kami_action.
Proof.
  induction acts; intros; simpl; auto.
  unfold ActionWb; intros.
  apply inversionSemAction in H3; dest; subst.
  specialize (H0 _ (in_eq _ _)) as P.
  specialize (P _ _ _ _ _ H1 H2 H4); dest; subst.
  assert (forall a, In a acts -> ActionWb (getKindAttr x6) a) as P0.
  { intros; apply H0; right; assumption. }
  specialize (IHacts H P0 (fun x => f ((Var _ (SyntaxKind k_in)) x5 :: x))).
  specialize (IHacts _ _ _ _ _ H1 H2 H5); dest.
  split.
  specialize (SubList_chain H1 H9 H6 (getKindAttr_map_fst _ _ H13)) as TMP; subst.
  - exists x6; repeat split; auto.
    + rewrite SubList_app_l_iff; split; auto.
    + econstructor; eauto.
  - rewrite map_app, SubList_app_l_iff; auto.
Qed.

Corollary gatherActionsWb_contWb_id k_in (acts : list (ActionT type k_in))
      k_out (cont : list (Expr type (SyntaxKind k_in)) -> ActionT type k_out) myRegs :
  (forall exprs, ActionWb myRegs (cont exprs)) ->
  (forall a,
      In a acts ->
      ActionWb myRegs a) ->
    ActionWb myRegs (GatherActions acts as vals; cont vals)%kami_action.
Proof.
  intros.
  specialize (gatherActionsWb_contWb _ cont H H0 (fun x => x)); simpl; auto.
Qed.

Lemma impl_readWb k size size' idx f :
  size <= size' ->
  ActionWb (map (fun x => (f x, SyntaxKind k)) (seq 0 size))
           (impl_read k size size' idx f).
Proof.
  unfold impl_read; intros.
  apply gatherActionsWb_contWb_id; unfold ActionWb; intros.
  - apply inversionSemAction in H2; dest; subst.
    induction size.
    + split; [|apply SubList_nil_l].
      exists nil; repeat split; try apply SubList_nil_l.
      econstructor; eauto.
    + rewrite seq_eq, map_app in *.
      rewrite SubList_app_l_iff in H1; dest.
      specialize (IHsize ltac:(lia) H1); dest.
      rewrite SubList_map_iff in H2; dest; simpl in *.
      split; [|apply SubList_nil_l].
      exists (x ++ x0); rewrite map_app.
      repeat split.
      * rewrite SubList_app_l_iff; split; auto.
      * apply SubList_nil_l.
      * apply f_equal2; auto.
      * eapply SemActionExpand; eauto.
        repeat intro; rewrite in_app_iff; auto.
  - rewrite in_map_iff in H0; dest; subst; destruct x; simpl in *.
    induction size.
    + exfalso; simpl in H4; contradiction.
    + unfold tag in *.
      rewrite seq_eq, map_app in *.
      rewrite tagApp, in_app_iff, map_length, seq_length, Nat.add_0_r in H4.
      repeat (apply inversionSemAction in H3; dest; subst).
      rewrite SubList_app_l_iff in H2; dest.
      destruct H4.
      * specialize (IHsize ltac:(lia) H4 H2); dest.
        rewrite SubList_map_iff in H3; dest.
        split.
        -- exists (x0 ++ x1); repeat split.
           ++ rewrite SubList_app_l_iff; split; auto.
           ++ apply SubList_app_r; assumption.
           ++ rewrite map_app.
              apply f_equal2; auto.
           ++ eapply SemActionExpand; eauto.
              repeat intro; rewrite in_app_iff; auto.
        -- apply SubList_nil_l.
      * rewrite SubList_map_iff in H2, H3; dest.
        assert (SubList [(s, existT _ (SyntaxKind k) x)] (x1 ++ x0)) as P.
        { simpl in H4; destruct H4; [|contradiction].
          inv H4; simpl in H5.
          assert (SubList [(f n, existT (fullType type) (SyntaxKind k) x)] o) as P.
          { repeat intro.
            destruct H4; subst; auto.
            inv H4. }
          specialize (SubList_chain H1 H3 P) as P0.
          rewrite <-fst_getKindAttr in P0.
          setoid_rewrite H5 in P0.
          rewrite (P0 ltac:(reflexivity)).
          repeat intro; rewrite in_app_iff; right; assumption. }
        split.
        -- exists (x1 ++ x0); repeat split; auto.
           ++ rewrite SubList_app_l_iff; auto.
           ++ rewrite map_app.
              apply f_equal2; auto.
           ++ repeat econstructor.
              apply (P _ (InSingleton _)).
        -- apply SubList_nil_l.
Qed.

Lemma replace_nth_n_le {A : Type} (l : list A) n val :
  length l <= n ->
  replace_nth l n val = l.
Proof.
  intros.
  unfold replace_nth.
  rewrite firstn_all2, skipn_all2, hd_error_nil; auto.
  repeat rewrite app_nil_r; reflexivity.
Qed.

Lemma replace_nth_n_lt {A : Type} val (l : list A):
  forall n,
  n < length l ->
  replace_nth l n val = (map (fun m => if (m =? n)%nat
                                       then val
                                       else nth_default val l m) (seq 0 (length l))).
Proof.
  assert (forall l',
             (map (fun m => nth_default val l' m) (seq 0 (length l'))) = l') as P.
  { induction l'; simpl; auto.
    unfold nth_default in *; simpl; f_equal.
    rewrite <- seq_shift, map_map.
    simpl; assumption. }
  induction l; simpl; intros; [lia|].
  rewrite <- seq_shift, map_map.
  unfold replace_nth in *.
  destruct n; simpl; f_equal.
  - rewrite <- (P l) at 1; unfold nth_default; simpl; reflexivity.
  - rewrite IHl; [|lia].
    apply map_ext_in; intros; unfold nth_default; reflexivity.
Qed.

Lemma impl_write_reduction k (l : list (type k)):
  forall (f : nat -> string) size size' (writeRq : type (WriteRq (Nat.log2_up size') k)),
    size <= size' ->
    size <= length l ->
    let idx := wordToNat (writeRq F1) in
    let val := writeRq (FS F1) in
    (forall n m, f n = f m -> n = m) ->
    forall reads upds calls retV,
      SemAction (valsToRegs k f (rev l))
                (impl_write size size' writeRq f) reads upds calls retV ->
      upds = (replace_nth (firstn size (valsToRegs k f (rev l)))
                                  idx (f idx, existT _ (SyntaxKind k) val))
      /\ calls = nil
      /\ retV = WO.
Proof.
  intros.
  assert (forall {A B : Type} (l : list A),
             l = concat (map fst (map (fun (x : A) => ([x], ((nil : list B), (Var type (SyntaxKind Void) WO)))) l))) as P.
  { clear.
    induction l; simpl; auto.
    rewrite IHl at 1; reflexivity. }
  assert (forall {A B : Type} (l : list A),
             nil = concat (map (fun x => fst (snd x))
                               (map (fun (x : A) => ([x], ((nil : list B), (Var type (SyntaxKind Void) WO)))) l))) as P0.
  { clear; intros; rewrite map_map.
    induction l; auto. }
  rewrite (P _ MethT (replace_nth _ _ _)).
  rewrite (P0 _ MethT (replace_nth (firstn size (valsToRegs k f (rev l)))
                                   idx (f idx, existT _ (SyntaxKind k) val))) at 1.
  unfold impl_write in H2.
  specialize
    gatherActions_effectful with (f := (fun x => ((Const _ (k := Void) Default)))) as Q.
  simpl in Q.
  eapply Q; eauto.
  clear P P0 H2 Q.
  destruct (le_lt_dec size idx).
  - rewrite replace_nth_n_le.
    + unfold valsToRegs.
      rewrite firstn_map, rev_length, map_map, firstn_seq_le; auto.
      induction size.
      * constructor.
      * unfold tag.
        rewrite seq_eq, map_app, tagApp.
        repeat rewrite map_app.
        apply Forall2_app.
        -- apply IHsize; lia.
        -- constructor; [|constructor].
           unfold SemAction_Effectful; simpl.
           intros.
           apply inversionSemAction in H2; dest; subst.
           apply inversionSemAction in H3; dest; subst.
           apply inversionSemAction in H5; dest; subst.
           split; simpl; auto.
           rewrite in_map_iff in H2; dest.
           apply inversionPair in H2; dest.
           rewrite (H1 _ _ H2) in *; EqDep_subst.
           destruct weq; auto.
           exfalso.
           rewrite map_length, seq_length, Nat.add_0_r in e.
           assert (@wordToNat (Nat.log2_up size') ($ size) = wordToNat (writeRq F1)) as P.
           { rewrite e; reflexivity. }
           rewrite wordToNat_natToWord_eqn, Nat.mod_small in P.
           ++ rewrite P in l0.
              unfold idx in l0.
              lia.
           ++ apply (Nat.lt_le_trans _ size'); [lia|].
              apply log2_up_pow2.
    + rewrite firstn_length_le; auto.
      unfold valsToRegs.
      rewrite map_length, rev_length, seq_length; assumption.
  - unfold valsToRegs.
    unfold replace_nth.
    rewrite firstn_map, skipn_map, firstn_seq_le, skipn_seq_le, Nat.add_0_l, tl_map, tl_seq;[| |rewrite rev_length]; try lia.
    + assert (size - idx <> 0) as P by lia.
      rewrite (seq_extract1 P idx).
      cbn [map hd_error].
      rewrite map_app, firstn_map, firstn_seq_le; [|lia].
      repeat rewrite map_app; repeat rewrite map_map.
      rewrite (@seq_app' 0 size idx), (@seq_app' (0 + idx) (size - idx) 1),
      Nat.add_0_l, Nat.add_1_r; try lia.
      unfold tag.
      repeat rewrite map_app.
      repeat rewrite tagApp.
      repeat rewrite map_app.
      rewrite Nat.add_0_r.
      repeat rewrite map_length, seq_length, Nat.add_1_l.
      cbn [seq].
      repeat apply Forall2_app.
      * assert (idx < size') as P0 by lia.
        clear - P0 l0 H1.
        enough (
            forall n,
              n <= idx ->
              Forall2
                (SemAction_Effectful (valsToRegs k f (rev l)))
                (map
                   (fun '(i, reg) =>
                      (Read val : k <- reg;
                       Write reg : k <-
                       IF Const type $ (i)%word ==
                          ReadStruct (Var _ (SyntaxKind (WriteRq (Nat.log2_up size') k)) writeRq)
                                     F1
         then ReadStruct (Var type (SyntaxKind (WriteRq (Nat.log2_up size') k)) writeRq) (FS F1)
         else Var type (SyntaxKind k) val; Retv)%kami_action) (tagFrom 0 (map f (seq 0 n))))
                (map
       (fun x =>
          ([(f x,
             existT _ (SyntaxKind k) (nth_default (evalConstT Default) (rev l) x))],
           ([], Var _ (SyntaxKind Void) WO))) (seq 0 n))).
        { apply H; auto. }
        induction n.
        -- constructor.
        -- intros;
             rewrite seq_eq, map_app, tagApp, map_length, seq_length, Nat.add_0_r, Nat.add_0_l.
           repeat rewrite map_app.
           apply Forall2_app.
           ++ apply IHn; lia.
           ++ constructor; [|constructor].
              unfold SemAction_Effectful; intros.
              apply inversionSemAction in H0; dest; subst.
              apply inversionSemAction in H2; dest; subst.
              apply inversionSemAction in H4; dest; subst.
              split; auto; simpl.
              unfold valsToRegs in H0.
              rewrite in_map_iff in H0; dest.
              apply inversionPair in H0; dest; EqDep_subst.
              rewrite (H1 _ _ H0) in *.
              destruct weq; simpl; auto.
              exfalso.
              assert (@wordToNat (Nat.log2_up size') ($ n) = wordToNat (writeRq F1)) as P.
              { rewrite e; reflexivity. }
              rewrite wordToNat_natToWord_eqn, Nat.mod_small in P.
              ** unfold idx in H.
                 rewrite P in H; lia.
              ** apply (Nat.lt_le_trans _ size'); [lia|].
                 apply log2_up_pow2.
      * constructor; [|constructor].
        repeat intro; simpl.
        apply inversionSemAction in H2; dest; subst.
        apply inversionSemAction in H3; dest; subst.
        apply inversionSemAction in H5; dest; subst.
        split; auto; simpl.
        destruct weq; auto.
        exfalso.
        rewrite map_length, seq_length in n.
        unfold idx in n.
        rewrite natToWord_wordToNat in n; contradiction.
      * simpl; rewrite map_length, seq_length.
        assert (size - idx - 1 = size - (S idx)) as P0 by lia.
        rewrite P0; clear P0 P.
        enough (
            forall n m,
              idx < n ->
              m + n <= size ->
              Forall2
                (SemAction_Effectful (valsToRegs k f (rev l)))
                (map
                   (fun '(i, reg) =>
                      (Read val : k <- reg;
                       Write reg : k <-
                       IF Const type $ (i)%word ==
                          ReadStruct (Var _ (SyntaxKind (WriteRq (Nat.log2_up size') k)) writeRq)
                                     F1
         then ReadStruct (Var type (SyntaxKind (WriteRq (Nat.log2_up size') k)) writeRq) (FS F1)
         else Var type (SyntaxKind k) val; Retv)%kami_action)
                   (tagFrom n (map f (seq n m))))
                (map
                   (fun x =>
                      ([(f x,
                         existT _ (SyntaxKind k) (nth_default (evalConstT Default) (rev l) x))],
                       ([], Var _ (SyntaxKind Void) WO))) (seq n m))) as P.
        { unfold valsToRegs in P; apply P; lia. }
        induction m; intros; [constructor|].
        rewrite seq_eq, map_app, tagApp.
        repeat rewrite map_app.
        apply Forall2_app.
        -- apply IHm; auto.
           lia.
        -- constructor; [|constructor].
           repeat intro.
           apply inversionSemAction in H4; dest; subst.
           apply inversionSemAction in H5; dest; subst.
           apply inversionSemAction in H7; dest; subst.
           split; auto.
           simpl.
           unfold valsToRegs in H4.
           rewrite in_map_iff in H4; dest.
           apply inversionPair in H4; dest; EqDep_subst.
           rewrite (H1 _ _ H4) in *.
           destruct weq; simpl; auto.
           exfalso.
           rewrite map_length, seq_length in e.
           assert (@wordToNat (Nat.log2_up size') $ (m + n) = wordToNat (writeRq F1)) as P.
              { rewrite e; reflexivity. }
              rewrite wordToNat_natToWord_eqn, Nat.mod_small in P.
              ** unfold idx in H2.
                 rewrite <- P in H2; lia.
              ** apply (Nat.lt_le_trans _ size'); [lia|].
                 apply log2_up_pow2.
Qed.

Lemma impl_writeWb k size size' writeRq f :
  size <= size' ->
  ActionWb (map (fun x => (f x, SyntaxKind k)) (seq 0 size))
           (@impl_write k size size' writeRq f).
Proof.
  intro.
  unfold impl_write.
  apply  gatherActionsWb_contWb_id; repeat intro.
  - apply inversionSemAction in H2; dest; subst.
    induction size; split.
    + exists nil; repeat split; try apply SubList_nil_l.
      econstructor; eauto.
    + apply SubList_nil_l.
    + rewrite seq_eq, map_app, SubList_app_l_iff in H1; dest.
      specialize (IHsize ltac:(lia) H1); dest.
      apply inversionSemAction in H7; dest; subst.
      simpl in H2.
      specialize (H2 _ (InSingleton _)).
      rewrite in_map_iff in H2; dest.
      exists (x ++ [x0]).
      repeat split.
      * rewrite SubList_app_l_iff; split; auto.
        repeat intro; inv H12; auto.
      * apply SubList_nil_l.
      * rewrite seq_eq; repeat rewrite map_app.
        f_equal; auto; simpl.
        rewrite H2; reflexivity.
      * econstructor; eauto.
    + apply SubList_nil_l.
  - rewrite in_map_iff in H0; dest; subst.
    destruct x.
    apply inversionSemAction in H3; dest; subst.
    apply inversionSemAction in H3; dest; subst.
    apply inversionSemAction in H6; dest; subst.
    induction size.
    + exfalso.
      inv H4.
    + unfold tag in *.
      rewrite seq_eq, map_app in *.
      rewrite tagApp, in_app_iff, Nat.add_0_l, Nat.add_0_r in H4.
      rewrite SubList_app_l_iff in H2; dest.
      destruct H4.
      * specialize (IHsize ltac:(lia) H4 H2); dest.
        apply inversionSemAction in H11; dest; subst.
        apply inversionSemAction in H12; dest; subst.
        apply inversionSemAction in H15; dest; subst.
        simpl in H6.
        specialize (H6 _ (InSingleton _)).
        rewrite in_map_iff in H6; dest.
        split.
        -- exists (x0 ++ [x2]); repeat split.
           ++ rewrite SubList_app_l_iff; split; auto.
              repeat intro; inv H19; auto.
              inv H20.
           ++ repeat intro; rewrite in_app_iff.
              inv H19; [|inv H20].
              inv H13; EqDep_subst.
              left; exact H11.
           ++ rewrite map_app; f_equal; auto.
              simpl; rewrite H6; reflexivity.
           ++ repeat econstructor.
              ** rewrite in_app_iff.
                 inv H13; EqDep_subst.
                 left; exact H11.
              ** rewrite map_app, in_app_iff.
                 left; exact H12.
              ** repeat intro.
                 inv H19.
        -- simpl.
           apply SubList_app_r.
           rewrite <- H10.
           repeat intro; inv H19;[| inv H20].
           exact H12.
      * simpl in H4; destruct H4; [|contradiction].
        rewrite map_length, seq_length in H4; inv H4.
        rewrite SubList_map_iff in H2, H6; dest.
        split.
        -- exists (x0 ++ x1).
           repeat split.
           ++ rewrite SubList_app_l_iff; split; auto.
           ++ repeat intro; inv H8; [| inv H9].
              rewrite in_app_iff.
              simpl in H7.
              destruct x1; [discriminate|]; inv H7.
              destruct x1; [|discriminate].
              assert (SubList [(f n, existT (fullType type) (SyntaxKind k) x)] o) as P.
              { repeat intro; inv H7; auto.
                inv H8. }
              specialize (SubList_chain H1 H6 P) as P0.
              simpl in P0; rewrite H9 in P0.
              rewrite P0; auto; right; left; rewrite H9; reflexivity.
           ++ rewrite map_app; f_equal; auto.
           ++ repeat econstructor.
              ** rewrite in_app_iff.
                 simpl in H7.
                 destruct x1; [discriminate|]; inv H7.
                 destruct x1; [|discriminate].
                 assert (SubList [(f n, existT (fullType type) (SyntaxKind k) x)] o) as P.
                 { repeat intro; inv H7; auto.
                   inv H8. }
                 specialize (SubList_chain H1 H6 P) as P0.
                 simpl in P0; rewrite H9 in P0.
                 rewrite P0; auto; right; left; rewrite H9; reflexivity.
              ** rewrite map_app, in_app_iff.
                 right; rewrite H7; simpl; auto.
              ** repeat intro.
                 inv H8.
        -- simpl.
           repeat intro; inv H8; [|inv H9].
           rewrite in_app_iff; right; simpl; auto.
Qed.

Lemma replace_nth_map_seq {A : Type} (f : nat -> A) (val : A) :
  forall start i size,
    i < size ->
    replace_nth (map f (seq start size)) i val =
    (map f (seq start i)) ++ [val] ++ (map f (seq (start + (S i)) (size - (S i)))).
Proof.
  intros.
  rewrite (split_seq start H); repeat rewrite map_app.
  unfold replace_nth.
  repeat rewrite firstn_app.
  repeat rewrite skipn_app.
  repeat rewrite firstn_map.
  repeat rewrite skipn_map.
  repeat rewrite map_length.
  repeat rewrite seq_length.
  rewrite diag; simpl.
  rewrite (@firstn_seq_le i start i (Nat.le_refl _)),
  (@skipn_seq_le i start i (Nat.le_refl _)),
  diag, app_nil_r.
  reflexivity.
Qed.

Section Proofs.
  Context `{Params : RegArray.Ifc.Params}.

  Local Notation Idx := (Bit (Nat.log2_up size)).
  Definition implRegArray := @Impl.impl Params.
  Definition specRegArray := @Spec.spec Params.

  Local Definition f := (fun i => name ++ "_" ++ natToHexStr i)%string.

  Record myRegArrayR (LocalRegs : RegsT) (arrayVal : Fin.t size -> type k)
         (o_i o_s : RegsT) : Prop :=
    {
      (* LocalRegs : RegsT; *)
      (* arrayVal : (Fin.t size -> type k); *)
      LocalRegVal : LocalRegs = valsToRegs k f (list_arr arrayVal);
      Ho_iCorrect : o_i = LocalRegs;
      Ho_sCorrect : o_s = [(RegArray.Spec.arrayName,
                            existT _ (SyntaxKind (Array size k)) arrayVal)];
    }.
      
  Ltac Record_destruct :=
    match goal with
    |[ H : exists _ _, myRegArrayR _ _ _ _ |- _] =>
     let LocalRegs := fresh "LocalRegs" in
     let arrayVal := fresh "arrayVal" in
     let H0 := fresh "H" in
     destruct H as [LocalRegs [arrayVal H0]]; destruct H0
    end.

  Local Lemma NoDup_f m n:
    NoDup (map f (seq m n)).
  Proof.
    induction n; [constructor|].
    rewrite seq_eq, map_app, NoDup_app_iff; repeat split; auto.
    - repeat constructor; intro; inv H.
    - repeat intro; inv H0; [|inv H1].
      rewrite in_map_iff in H; dest.
      unfold f in H; repeat rewrite append_remove_prefix in H.
      rewrite in_seq in H0.
      apply natToHexStr_inj in H.
      lia.
    - repeat intro; inv H; [|inv H1].
      rewrite in_map_iff in H0; dest.
      unfold f in H; repeat rewrite append_remove_prefix in H.
      rewrite in_seq in H0.
      apply natToHexStr_inj in H.
      lia.
  Qed.
  
  Goal RegArrayCorrect implRegArray specRegArray.
    econstructor 1 with (regArrayR := (fun o1 o2 =>
                                         (exists LocalRegs arrayVal,
                                             myRegArrayR LocalRegs arrayVal o1 o2)))
                        (regArrayRegs := map (fun name => (name, SyntaxKind k)) Impl.names).
    all : unfold read, write, implRegArray, specRegArray, impl, spec,
                   Impl.impl, Impl.read, Impl.write,
                   Spec.read, Spec.write, Utila.tag; intros.
    - red; intros; try Record_destruct.
      assert (length (rev (list_arr arrayVal)) = size) as P.
      { rewrite rev_length, <- list_arr_length; reflexivity. }
      assert (forall n m, f n = f m -> n = m) as P0.
      { unfold f; intros.
        repeat rewrite append_remove_prefix in H.
        apply natToHexStr_inj in H; assumption. }
      specialize (impl_read_reduction (rev (list_arr arrayVal)) f) as P1.
      rewrite P, rev_involutive in P1.
      specialize (P1 idx P0 reads_i upds calls retval).
      unfold impl_read in P1.
      rewrite Ho_iCorrect0, LocalRegVal0 in H0.
      unfold Impl.names, valsToRegs in H0.
      unfold f, tag in P1.
      specialize (P1 H0); dest; subst.
      repeat split; auto.
      exists [(Spec.arrayName, existT _ (SyntaxKind (Array size k)) arrayVal)].
      econstructor 5; eauto.
      + constructor; reflexivity.
      + econstructor; auto.
        cbn [evalExpr].
        rewrite <- list_arr_correct.
        destruct lt_dec; auto.
    - specialize (@impl_readWb k size size idx f (le_n _)) as P.
      unfold impl_read, f in P.
      unfold Impl.names.
      rewrite map_map.
      apply P.
    - red; intros; try Record_destruct.
      assert (length (rev (list_arr arrayVal)) = size) as P.
      { rewrite rev_length, <- list_arr_length; reflexivity. }
      assert (forall n m, f n = f m -> n = m) as P0.
      { unfold f; intros.
        repeat rewrite append_remove_prefix in H.
        apply natToHexStr_inj in H; assumption. }
      specialize (impl_write_reduction (rev (list_arr arrayVal)) f) as P1.
      rewrite P, rev_involutive in P1.
      rewrite Ho_iCorrect0, LocalRegVal0 in H0.
      unfold Impl.names, valsToRegs in H0.
      unfold f, tag in P1.
      specialize (P1 _ _ _ (Nat.le_refl _) (Nat.le_refl _) P0 _ _ _ _ H0); dest; subst.
      do 2 eexists; split.
      + repeat econstructor.
        * repeat intro; inv H.
      + destruct (le_lt_dec size (wordToNat (val F1))).
        * do 2 eexists.
          econstructor 1 with (arrayVal := arrayVal).
          -- reflexivity.
          -- unfold valsToRegs, f.
             rewrite <- list_arr_length, firstn_all2; [|rewrite map_length, seq_length; auto].
             rewrite replace_nth_n_le; [|rewrite map_length, seq_length; auto].
             apply doUpdRegs_idemp.
             rewrite map_map; simpl.
             clear - P0; induction size.
             ++ constructor.
             ++ rewrite seq_eq, map_app, NoDup_app_iff; repeat split; auto; repeat intro.
                ** constructor; auto.
                   constructor.
                ** inv H0; [|inv H1].
                   rewrite in_map_iff in H; dest.
                   specialize (P0 _ _ H).
                   rewrite in_seq in H0; subst; lia.
                ** inv H; [|inv H1].
                   rewrite in_map_iff in H0; dest.
                   specialize (P0 _ _ H).
                   rewrite in_seq in H0; subst; lia.
          -- simpl; rewrite String.eqb_refl.
             repeat f_equal.
             apply functional_extensionality; intros.
             destruct weq; simpl; auto.
             exfalso.
             specialize (fin_to_nat_bound x) as P1.
             rewrite e, wordToNat_natToWord_eqn, Nat.mod_small in l; try lia.
             apply (lt_le_trans _ size); auto.
             apply log2_up_pow2.
        * do 2 eexists; econstructor 1 with (arrayVal := (fun i =>
                                              if getBool (weq (val F1) $ (proj1_sig (to_nat i)))
                                              then val (FS F1)
                                              else arrayVal i)).
          -- reflexivity.
          -- unfold valsToRegs, f.
             rewrite <- list_arr_length, firstn_all2; [|rewrite map_length, seq_length; auto].
             rewrite <- list_arr_length.
             rewrite replace_nth_map_seq, Nat.add_0_l; auto.
             rewrite (split_seq 0 l); repeat rewrite map_app.
             repeat rewrite doUpdRegs_app_r; repeat rewrite doUpdRegs_app_l.
             repeat apply f_equal2.
             ++ match goal with
                | [|- doUpdRegs _ (doUpdRegs ?a (doUpdRegs ?b ?c)) = _]
                  => rewrite (@doUpdRegs_DisjKey c b);[rewrite (@doUpdRegs_DisjKey c a) |]
                end.
                ** rewrite doUpdRegs_idemp.
                   --- apply map_ext_in; intros.
                       rewrite in_seq in H.
                       do 2 f_equal.
                       repeat rewrite <-list_arr_correct.
                       destruct lt_dec; auto.
                       destruct weq; auto.
                       exfalso.
                       rewrite e, to_nat_of_nat, wordToNat_natToWord_eqn, Nat.mod_small in H;
                         [simpl in H; lia|].
                       simpl.
                       apply (lt_le_trans _ size); auto.
                       apply log2_up_pow2.
                   --- rewrite map_map; simpl.
                       apply NoDup_f.
               ** repeat intro; rewrite map_map; simpl.
                  destruct (string_dec
                              (name ++ String "_" (natToHexStr (wordToNat (val F1)))) k).
                  --- right; intro.
                      rewrite in_map_iff in H; dest.
                      rewrite <- H in e.
                      repeat rewrite (append_cons "_" (natToHexStr _)) in e.
                      repeat rewrite append_remove_prefix in e.
                      apply natToHexStr_inj in e.
                      rewrite in_seq in H1; lia.
                  --- left; intro; destruct H; contradiction.
               ** repeat intro; repeat rewrite map_map; simpl.
                  destruct (in_dec string_dec k
                                   (map (fun x => (name ++ String "_" (natToHexStr x))%string)
                                        (seq 0 (wordToNat (val F1))))).
                  --- left; intro.
                      rewrite in_map_iff in i, H; dest.
                      rewrite <- H in H2.
                      repeat rewrite (append_cons "_" (natToHexStr _)) in H2.
                      repeat rewrite append_remove_prefix in H2.
                      apply natToHexStr_inj in H2.
                      rewrite in_seq in *.
                      lia.
                  --- right; assumption.
             ++ cbn [map Nat.add].
                match goal with
                | [|- doUpdRegs _ (doUpdRegs _ (doUpdRegs ?a ?b)) = _]
                  => rewrite (@doUpdRegs_DisjKey b a)
                end.
                ** unfold doUpdRegs at 2.
                   cbn [findReg fst snd].
                   rewrite String.eqb_refl, doUpdReg_doUpdRegs, doUpdReg_notIn.
                   --- do 3 f_equal.
                       rewrite <- list_arr_correct.
                       destruct lt_dec; [destruct weq|]; auto.
                       +++ exfalso.
                           apply n.
                           rewrite to_nat_of_nat; simpl.
                           rewrite natToWord_wordToNat; reflexivity.
                       +++ exfalso; contradiction.
                   --- rewrite map_map; simpl; intro.
                       rewrite in_map_iff in H; dest.
                       repeat rewrite (append_cons "_" (natToHexStr _)) in H.
                       repeat rewrite append_remove_prefix in H.
                       apply natToHexStr_inj in H.
                       rewrite in_seq in H1.
                       lia.
                ** intro; rewrite map_map; cbn [map fst].
                   destruct (in_dec string_dec k
                                    (map (fun x : nat => (name ++ "_" ++ natToHexStr x)%string)
                                         (seq (S (wordToNat (val F1)))
                                              (size - S (wordToNat (val F1)))))); auto.
                   right; intro.
                   inv H; [|inv H1].
                   rewrite in_map_iff in i; dest.
                   repeat rewrite append_remove_prefix in H.
                   apply natToHexStr_inj in H.
                   rewrite in_seq in H1.
                   lia.
             ++ rewrite Nat.add_0_l.
                match goal with
                | [ |- doUpdRegs _ (doUpdRegs _ (doUpdRegs ?a ?a)) = _]
                    => rewrite (doUpdRegs_idemp a)
                end.
                ** rewrite oneUpdRegs_doUpdRegs, oneUpdRegs_notIn.
                   --- rewrite doUpdRegs_DisjKey.
                       +++ apply map_ext_in; intros.
                           do 2 f_equal.
                           repeat rewrite <- list_arr_correct.
                           destruct lt_dec; auto.
                           destruct weq; auto.
                           exfalso.
                           rewrite to_nat_of_nat in e.
                           rewrite e, in_seq in H.
                           simpl in H; destruct H.
                           rewrite wordToNat_natToWord_eqn, Nat.mod_small in H; [lia|].
                           apply (lt_le_trans _ size); auto.
                           apply log2_up_pow2.
                       +++ intro; repeat rewrite map_map; cbn [map fst].
                           destruct (in_dec string_dec k
                                            (map (fun x => (name ++ "_" ++ natToHexStr x)%string)
                                                 (seq (S (wordToNat (val F1)))
                                                      (size - S (wordToNat (val F1)))))); auto.
                           left; intro.
                           rewrite in_map_iff in *; dest; subst.
                           rewrite in_seq in *.
                           repeat rewrite append_remove_prefix in H.
                           apply natToHexStr_inj in H.
                           lia.
                   --- rewrite map_map; cbn [fst]; intro.
                       rewrite in_map_iff in *; dest; subst.
                       rewrite in_seq in *.
                       repeat rewrite append_remove_prefix in H.
                       apply natToHexStr_inj in H.
                       lia.
                ** rewrite map_map.
                   cbn [fst].
                   apply NoDup_f.
          -- simpl; rewrite String.eqb_refl; reflexivity.
    - specialize (@impl_writeWb k _ _ val f (Nat.le_refl _)) as P.
      unfold impl_write, f, Impl.names, tag in *.
      rewrite map_map.
      apply P.
  Qed.
End Proofs.
