Require Import Kami.All.
Require Import StdLibKami.RegArray.Impl.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.Spec.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import Kami.GallinaModules.Relations.
Require Import Coq.Logic.EqdepFacts.

Lemma snd_tagFrom {A : Type} (l : list A):
  forall n,
    map snd (tagFrom n l) = l.
Proof.
  induction l; simpl; auto; intros.
  f_equal; apply IHl.
Qed.

Lemma fst_tagFrom {A : Type} (l : list A):
  forall n,
    map fst (tagFrom n l) = seq n (length l).
Proof.
  induction l; simpl; auto; intros.
  f_equal; apply IHl.
Qed.

Corollary length_tagFrom {A : Type} (l : list A):
  forall n,
    length (tagFrom n l) = length l.
Proof.
  intros.
  rewrite <- (snd_tagFrom l n) at 2.
  rewrite map_length; reflexivity.
Qed.

Lemma tagFrom_n {A : Type} (l : list A):
  forall n t,
    In t (tagFrom n l) ->
    n <= fst t < (n + length l).
Proof.
  induction l; simpl; intros; [contradiction|].
  destruct H; subst; simpl; [|specialize (IHl _ _ H)]; lia.
Qed.


Lemma tagFromO_Correct {A : Type} (l  : list A): 
  forall t n,
    In t (tagFrom n l) ->
    nth_error l ((fst t) - n) = Some (snd t).
Proof.
  induction l; simpl; intros; [contradiction|].
  destruct H; subst; simpl.
  - rewrite Nat.sub_diag; simpl; reflexivity.
  - specialize (IHl _ _ H).
    specialize (tagFrom_n _ _ _ H) as P0.
    rewrite app_cons, nth_error_app2; simpl; try lia.
    rewrite <- IHl.
    f_equal; lia.
Qed.

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

Lemma tagApp {A : Type} (l1 l2 : list A):
  forall m,
    tagFrom m (l1 ++ l2) = tagFrom m l1 ++ tagFrom (length l1 + m) l2.
Proof.
  induction l1; simpl; auto; intros.
  f_equal.
  rewrite <- Nat.add_succ_r.
  apply IHl1.
Qed.

Lemma evalExpr_Kor_idemp k (e1 : Expr type (SyntaxKind k)):
  evalKorOpBin k (evalExpr e1) (evalExpr e1) = (evalExpr e1).
Proof.
  induction k; simpl.
  - apply orb_diag.
  - apply wor_idemp.
  - apply functional_extensionality_dep; intros.
    apply (H x (Var _ (SyntaxKind (k x)) (evalExpr e1 x))).
  - apply functional_extensionality_dep; intros.
    apply (IHk (Var _ (SyntaxKind k) (evalExpr e1 x))).
Qed.

Local Lemma Kor_default_rev k (l : list (Expr type (SyntaxKind k))):
  (forall a,
    In a (rev l) ->
    a = Const type Default) ->
    evalExpr (@Kor _ k (rev l)) = evalExpr (Const type Default).
Proof.
  cbn [evalExpr].
  unfold evalKorOp.
  rewrite <- fold_left_rev_right, map_rev, rev_involutive.
  induction l; intros; simpl in *; subst; auto.
  rewrite IHl.
  - rewrite (H _ (in_or_app _ _ _ (or_intror _ (InSingleton _)))); simpl.
    assert (evalConstT Default = (evalExpr (@Const type k Default))) as P by reflexivity.
    repeat rewrite P.
    apply evalExpr_Kor_idemp.
  - intros; apply H; rewrite in_app_iff; left; assumption.
Qed.

Local Lemma Kor_default_rev' k (l : list (Expr type (SyntaxKind k))):
  (forall a,
    In (evalExpr a) (map (fun x => evalExpr x) (rev l)) ->
    (evalExpr a) = (evalExpr (Const type Default))) ->
    evalExpr (@Kor _ k (rev l)) = evalExpr (Const type Default).
Proof.
  cbn [evalExpr].
  unfold evalKorOp.
  repeat rewrite map_rev.
  rewrite <- fold_left_rev_right, rev_involutive.
  induction l; intros; simpl in *; subst; auto.
  rewrite IHl.
  - rewrite (H _ (in_or_app _ _ _ (or_intror _ (InSingleton _)))); simpl.
    assert (evalConstT Default = (evalExpr (@Const type k Default))) as P by reflexivity.
    repeat rewrite P.
    apply evalExpr_Kor_idemp.
  - intros; apply H; rewrite in_app_iff; left; assumption.
Qed.

Lemma Kor_default k (l : list (Expr type (SyntaxKind k))):
  (forall a,
      In a l ->
      a = Const type Default) ->
  evalExpr (@Kor _ k l) = evalExpr (Const type Default).
Proof.
  setoid_rewrite <- rev_involutive.
  apply Kor_default_rev.
Qed.

Lemma Kor_default' k (l : list (Expr type (SyntaxKind k))):
  (forall a,
      In (evalExpr a) (map (fun x => evalExpr x) l) ->
      (evalExpr a) = (evalExpr (Const type Default))) ->
  evalExpr (@Kor _ k l) = evalExpr (Const type Default).
Proof.
  setoid_rewrite <- (rev_involutive l).
  apply Kor_default_rev'.
Qed.

Lemma Expr_type_dec {k} (e1 e2 : Expr type (SyntaxKind k)):
  {e1 = e2} + {e1 <> e2}.
  destruct (kami_exprs_eq_dec (NormExpr e1) (NormExpr e2)).
  - left; inv e; reflexivity.
  - right; intro; apply n; rewrite H; reflexivity.
Qed.
  
Local Lemma Kor_sparse_rev k (l : list (Expr type (SyntaxKind k))):
  forall (val : Expr type (SyntaxKind k)),
    In (evalExpr val) (map (fun x => evalExpr x) (rev l)) ->
    (forall a,
        In (evalExpr a) (map (fun x => evalExpr x) (rev l)) ->
        (evalExpr a) = (evalExpr val) \/ (evalExpr a) = (evalExpr (Const type Default))) ->
    evalExpr (@Kor _ k (rev l)) =  evalExpr val.
Proof.
  intros.
  cbn [evalExpr].
  unfold evalKorOp.
  rewrite <- fold_left_rev_right, map_rev, rev_involutive.
  induction l; intros; simpl in *; dest; subst; [contradiction|rewrite map_app in *].
  rewrite in_app_iff in H; destruct H.
  - rewrite IHl; auto.
    + destruct (H0 _ (in_or_app _ _ _ (or_intror _ (InSingleton _)))); rewrite H1.
      * apply evalExpr_Kor_idemp.
      * apply evalExpr_Kor_Default.
    + intros.
      apply H0; rewrite in_app_iff; left; assumption.
  - inv H; [|contradiction].
    destruct (In_dec (isEq k) (evalExpr val) (map (fun x => evalExpr x) (rev l))).
    + rewrite IHl, H1; auto.
      * apply evalExpr_Kor_idemp.
      * intros.
        apply H0; rewrite in_app_iff; left; assumption.
    + assert (forall a, In (evalExpr a) (map (fun x => evalExpr x) (rev l))
                                         -> (evalExpr a) = (evalExpr (Const type Default))) as P.
      { intros.
        destruct (H0 _ (in_or_app _ _ _ (or_introl _ H))); subst; auto.
        rewrite H2 in H.
        exfalso; contradiction.
      }
      specialize (Kor_default_rev' l) as P0.
      cbn [evalExpr] in P0.
      unfold evalKorOp in P0.
      repeat rewrite map_rev in P0.
      rewrite <- fold_left_rev_right, rev_involutive in P0.
      setoid_rewrite P0; [|rewrite <-map_rev; auto].
      rewrite H1.
      assert (@evalConstT k Default = evalExpr (Const type Default)) as P1 by reflexivity.
      rewrite P1, evalExpr_Kor_comm.
      apply evalExpr_Kor_Default.
Qed.

Lemma Kor_sparse k (l : list (Expr type (SyntaxKind k))):
  forall val,
    In (evalExpr val) (map (fun x => evalExpr x) l) ->
    (forall a,
        In (evalExpr a) (map (fun x => evalExpr x) l) ->
        (evalExpr a) = (evalExpr val) \/ (evalExpr a) = (evalExpr (Const type Default))) ->
    evalExpr (@Kor _ k l) =  evalExpr val.
Proof.
  setoid_rewrite <- (rev_involutive l).
  apply Kor_sparse_rev.
Qed.

Lemma evalExpr_Kor_Default_l k (e : Expr type (SyntaxKind k)):
  evalKorOpBin k (evalConstT Default) (evalExpr e) = evalExpr e.
Proof.
  assert (@evalConstT k Default = evalExpr (Const type Default)) as P by reflexivity.
  rewrite P, evalExpr_Kor_comm.
  apply evalExpr_Kor_Default.
Qed.

Definition sparseList {A : Type} (def : A) (l : list A) (n size : nat) :=
  map (fun x => if Nat.eqb x n then nth_default def l n else def) (seq 0 size).

Definition sparseList' {A: Type} (def : A) (l : list A) (n : nat) :=
  sparseList def l n (length l).

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

Lemma seq_nth_error_Some size m n :
  n < size <->
  nth_error (seq m size) n = Some (m + n).
Proof.
  red; split.
  - induction size; intros; [lia|].
    apply lt_n_Sm_le in H.
    rewrite seq_eq.
    destruct (le_lt_or_eq _ _ H).
    + rewrite nth_error_app1; auto.
      rewrite seq_length; assumption.
    + rewrite nth_error_app2; subst.
      * rewrite seq_length, diag.
        reflexivity.
      * rewrite seq_length; assumption.
  - intros.
    assert (nth_error (seq m size) n <> None) as P.
    { intro P; rewrite P in H; discriminate. }
    rewrite nth_error_Some, seq_length in P.
    assumption.
Qed.


Lemma seq_nth_error_None size m n :
  size <= n <->
  nth_error (seq m size) n = None.
Proof.
  rewrite nth_error_None, seq_length; reflexivity.
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

Lemma Zlor_bounds sz m n :
  (0 <= m < 2 ^ sz ->
   0 <= n < 2 ^ sz ->
   0 <= Z.lor m n < 2 ^ sz)%Z.
Proof.
  intros; split; dest.
  - rewrite Z.lor_nonneg; auto.
  - destruct (Zle_lt_or_eq _ _ H), (Zle_lt_or_eq _ _ H0).
    + rewrite Z.log2_lt_pow2 in *; auto.
      * rewrite Z.log2_lor; auto.
        apply Z.max_lub_lt; auto.
      * specialize ((proj2 (Z.lor_nonneg m n)) (conj H H0)) as P.
        destruct (Zle_lt_or_eq _ _ P); auto.
        exfalso.
        symmetry in H5.
        rewrite Z.lor_eq_0_iff in H5; lia.
    + rewrite <- H4, Z.lor_0_r; assumption.
    + rewrite <- H3, Z.lor_0_l; assumption.
    + rewrite <- H3, Z.lor_0_l; assumption.
Qed.

Lemma wor_assoc n (x y z : word n):
  wor x (wor y z) = wor (wor x y) z.
Proof.
  arithmetizeWord.
  - rewrite (Zmod_small _ _ (Zlor_bounds _ H0 H)),
    (Zmod_small _ _ (Zlor_bounds _ H1 H0)),
    Z.lor_assoc; reflexivity.
Qed.

Lemma evalExpr_Kor_assoc k (e1 e2 e3 : Expr type (SyntaxKind k)):
  evalKorOpBin k (evalExpr e1) (evalKorOpBin k (evalExpr e2) (evalExpr e3)) =
  evalKorOpBin k (evalKorOpBin k (evalExpr e1) (evalExpr e2)) (evalExpr e3).
Proof.
  induction k; simpl.
  - apply orb_assoc.
  - apply wor_assoc.
  - apply functional_extensionality_dep; intros.
    apply (H _ (Var _ (SyntaxKind (k x)) (evalExpr e1 x))
             (Var _ (SyntaxKind (k x)) (evalExpr e2 x))
             (Var _ (SyntaxKind (k x)) (evalExpr e3 x))).
  - apply functional_extensionality_dep; intros.
    apply (IHk (Var _ (SyntaxKind k) (evalExpr e1 x))
             (Var _ (SyntaxKind k) (evalExpr e2 x))
             (Var _ (SyntaxKind k) (evalExpr e3 x))).
Qed.

Local Lemma evalExpr_Kor_perm_rev k (l : list (Expr type (SyntaxKind k))) :
  forall l',
    l [=] l' ->
    evalExpr (Kor (rev l)) = evalExpr (Kor (rev l')).
Proof.
  induction 1; auto.
  - cbn [evalExpr] in *.
    unfold evalKorOp in *.
    repeat rewrite <- fold_left_rev_right, map_rev, rev_involutive in *.
    simpl.
    setoid_rewrite IHPermutation.
    reflexivity.
  - cbn [evalExpr].
    unfold evalKorOp.
    repeat rewrite <- fold_left_rev_right, map_rev, rev_involutive.
    simpl.
    assert (evalExpr (Var _ (SyntaxKind k)
                          (fold_right (fun y0 x0 => evalKorOpBin k x0 y0) (evalConstT Default)
                                      (map (evalExpr (exprT:=SyntaxKind k)) l))) =
            (fold_right (fun y0 x0 => evalKorOpBin k x0 y0) (evalConstT Default)
                        (map (evalExpr (exprT:=SyntaxKind k)) l))) as P by reflexivity.
    setoid_rewrite <- P.
    rewrite <- evalExpr_Kor_assoc, evalExpr_Kor_comm, evalExpr_Kor_assoc; reflexivity.
  - rewrite IHPermutation1, IHPermutation2; reflexivity.
Qed.

Lemma evalExpr_Kor_perm k (l : list (Expr type (SyntaxKind k))) :
  forall l',
    l [=] l' ->
    evalExpr (Kor l) = evalExpr (Kor l').
Proof.
  intros.
  rewrite (Permutation.Permutation_rev l), (Permutation.Permutation_rev l')  in H.
  rewrite <- (rev_involutive l),  <- (rev_involutive l').
  apply evalExpr_Kor_perm_rev; assumption.
Qed.

Lemma evalExpr_Kor_head k (e : Expr type (SyntaxKind k)) (l : list (Expr type (SyntaxKind k))):
  evalExpr (Kor (e :: l)) = evalKorOpBin k (evalExpr e) (evalExpr (Kor l)).
Proof.
  rewrite (evalExpr_Kor_perm (Permutation.Permutation_rev (e :: l))),
  (evalExpr_Kor_perm (Permutation.Permutation_rev l)) at 1.
  cbn [evalExpr].
  unfold evalKorOp.
  repeat rewrite <- fold_left_rev_right, map_rev, rev_involutive.
  simpl.
  assert ((fold_right (fun y x : type k => evalKorOpBin k x y) (evalConstT Default)
                      (map (evalExpr (exprT:=SyntaxKind k)) l)) =
          evalExpr (Var _ (SyntaxKind k)
                        (fold_right (fun y x : type k => evalKorOpBin k x y) (evalConstT Default)
                                    (map (evalExpr (exprT:=SyntaxKind k)) l)))) as P
      by reflexivity.
  setoid_rewrite P.
  rewrite evalExpr_Kor_comm; reflexivity.
Qed.

Lemma length_sparseList {A : Type} (def : A) (l : list A) (n size : nat) :
  length (sparseList def l n size) = size.
Proof.
  unfold sparseList.
  rewrite map_length, seq_length; reflexivity.
Qed.

Lemma tagFrom_tag' m {A : Type} (l : list A) :
  tagFrom m l = tag' m l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma list_arr_length {A : Type} n :
  forall (arr : t n -> A),
    n = length (list_arr arr).
Proof.
  unfold list_arr; intros.
  rewrite map_length, getFins_length; reflexivity.
Qed.

Lemma arr_nth_Fin' {A : Type} :
  forall m (arr : t m -> A),
    arr = (nth_Fin' _ (list_arr_length arr)).
Proof.
  intros.
  apply functional_extensionality; intros.
  rewrite (nth_Fin'_nth (arr x)).
  rewrite <- nth_default_eq, <- list_arr_correct.
  destruct lt_dec.
  - specialize (of_nat_to_nat_inv x) as P.
    rewrite (of_nat_ext l (proj2_sig (to_nat x))), P; reflexivity.
  - exfalso.
    apply n, fin_to_nat_bound.
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

Lemma evalExpr_Kor_same_eval (k : Kind) (l l' : list (Expr type (SyntaxKind k))) :
  Forall2 (fun x y => evalExpr x = evalExpr y) l l' ->
  evalExpr (Kor l) = evalExpr (Kor l').
Proof.
  induction 1; auto.
  repeat rewrite evalExpr_Kor_head.
  rewrite H, IHForall2; reflexivity.
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

Section Proofs.
  Context `{Params : RegArray.Ifc.Params}.
  Record RegArrayCorrect (imp spec: RegArray.Ifc.Ifc): Type :=
  {
    regArrayRegs : list (Attribute FullKind);
    regArrayR : RegsT -> RegsT -> Prop;
    readCorrect : forall idx, EffectfulRelation regArrayR (@read _ imp type idx) (@read _ spec type idx);
    readWb : forall idx, ActionWb regArrayRegs (@read _ imp type idx);
    writeCorrect : forall val, EffectfulRelation regArrayR (@write _ imp type val) (@write _ spec type val);
    writeWb : forall val, ActionWb regArrayRegs (@write _ imp type val);
  }.

  Local Notation Idx := (Bit (Nat.log2_up size)).
  Definition implRegArray := @Impl.impl Params.
  Definition specRegArray := @Spec.spec Params.

  Variable arrayVal : (Fin.t size -> type k).
  Local Definition f := (fun i => name ++ "_" ++ natToHexStr i)%string.
  Local Definition LocalRegs := valsToRegs k f (list_arr arrayVal).

  (* Definition eqVals (r : RegT) (af : Attribute (type (Idx))) : Prop := *)
  (*   r = (fst af, existT _ (SyntaxKind (Idx)) (snd af)). *)

  Record myRegArrayR (o_i o_s : RegsT) : Prop :=
    {
      (* LocalRegs : RegsT; *)
      (* ArrayReg : RegT; *)
      (* RegListVals : list (type Idx); *)
      (* arrayVal : (Fin.t size -> type k); *)
      (* HLocalRegsSz : length LocalRegs = size; *)
      (* HNameCorrect : forall n (pf : n < size), nth_error LocalRegs n *)
      (*                                          = Some (nth_default "" Impl.names n, existT _ (SyntaxKind k) (arrayVal (of_nat_lt pf))); *)
      Ho_iCorrect : o_i = LocalRegs;
      Ho_sCorrect : o_s = [(RegArray.Spec.arrayName,
                            existT _ (SyntaxKind (Array size k)) arrayVal)];
      (* Ho_iNoDup : NoDup (map fst o_i); *)
    }.
      
  Ltac Record_destruct :=
    match goal with
    |[ H : myRegArrayR _ _ |- _] => destruct H
    end.
  
  Ltac extract_gatherActions' subRegs1 subRegs2:=
    match goal with
    | [ H : SemAction ?o (gatherActions (map ?f ?l) ?s) _ _ _ _ |- _]
      => let HCont := fresh "H" in
         let HBody := fresh "H" in
         let P := fresh "H" in
         assert (forall y, ActionWb (getKindAttr (subRegs1++subRegs2)) (s y)) as HCont
         ; [ intros
             ; eapply ActionWbExpand with (myRegs1 := getKindAttr subRegs2)
              ;[ try sublist_sol 
               | try (unfold ActionWb; intros; hyp_consumer1; basic_goal_consumer)]
           | assert(forall t,
                       fst t < size ->
                       snd t = nth_default "" Impl.names (fst t) ->
                       ActionWb (getKindAttr (subRegs1 ++ subRegs2)) (f t)) as HBody
             ;[intros
               ;eapply ActionWbExpand with (myRegs1 := getKindAttr subRegs1)
               ;[ sublist_sol
                | ]
              |]
         ]
    end.
  
  Goal RegArrayCorrect implRegArray specRegArray.
    econstructor 1 with (regArrayR := myRegArrayR)
                        (regArrayRegs := map (fun name => (name, SyntaxKind k)) Impl.names).
    all : try red; unfold read, write, implRegArray, specRegArray, impl, spec,
                   Impl.impl, Impl.read, Impl.write,
                   Spec.read, Spec.write, Utila.tag; intros; try Record_destruct; repeat split.
  Admitted.
End Proofs.
