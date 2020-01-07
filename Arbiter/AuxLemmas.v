Require Import Kami.All.

Lemma InGetKindAttr: forall {name} {o: RegsT} {k} {v} (H: In (name, existT (fullType type) (SyntaxKind k) v) o),
    In (name, SyntaxKind k) (getKindAttr o).
Proof.
  intros; rewrite in_map_iff; eexists; split; eauto; simpl; reflexivity.
Qed.

Lemma doUpdRegs_nil: forall r,
    doUpdRegs [] r = r.
Proof.
  intros.
  induction r; auto.
  simpl.
  rewrite IHr.
  auto.
Qed.

Lemma in_app_fst: forall {A} {B} {a: A} {l l': list (A * B)},
    ~ In a (map fst l) ->
    In a (map fst (l ++ l')) ->
    In a (map fst l').
Proof.
  intros.
  induction l, l'; simpl in *; auto; intuition.
Qed.

Lemma inImpInFst: forall {A B: Type} (a: A) (b: B) (l: list (A * B)),
    In (a,b) l ->
    In a (map fst l).
Proof.
  intros; rewrite in_map_iff; exists (a, b); auto.
Qed.

Lemma noDupSame: forall (o_s: RegsT),
    List.NoDup (map fst o_s) ->
    forall name k rv_1 rv_2,
      In (name, existT (fullType type) (SyntaxKind k) rv_1) o_s ->
      In (name, existT (fullType type) (SyntaxKind k) rv_2) o_s ->
      rv_1 = rv_2.
Proof.
  induction o_s; intros; simpl in *; intuition; subst.
  - apply inversionPairExistT in H0; inv H0; EqDep_subst; reflexivity.
  - exfalso.
    inv H; apply H3; apply (in_map fst) in H0; auto.
  - exfalso.
    inv H; apply H3; apply (in_map fst) in H2; auto.
  - inv H; eapply IHo_s; eauto.
Qed.

Lemma SubList_Strengthen: forall A (l1 l2: list A) (a: A),
    SubList l1 (a::l2) ->
    ~ In a l1 ->
    SubList l1 l2.
Proof.
  intros.
  unfold SubList in *.
  intros.
  specialize (H x H1).
  inversion H; subst; solve [intuition].
Qed.

Lemma getKindAttrEqImpFstEq: forall (r1 r2: RegsT), (* Possibly replace *)
    getKindAttr r1 = getKindAttr r2 ->
    map fst r1 = map fst r2.
Proof.
  apply getKindAttr_fst.
Qed.

Lemma inGetKindAttrImpInMapFstRegs: forall (r: RegsT) a k,
    In (a, k) (getKindAttr r) ->
    In a (map fst r).
Proof.
  intros.
  erewrite <- fst_getKindAttr, in_map_iff; exists (a, k); eauto.
Qed.

Lemma inFstGetKindAttrIffInFst: forall (r: RegsT) a,
    In a (map fst (getKindAttr r)) <->
    In a (map fst r).
Proof.
  intros; split; intros;
    [rewrite <- fst_getKindAttr | rewrite fst_getKindAttr]; assumption.
Qed.

Lemma stripIrrelevantUpd: forall (name: string) (regs: RegsT) (upds: list RegT) v,
    ~ In name (map fst regs) ->
    doUpdRegs ((name, v) :: upds) regs = doUpdRegs upds regs.
  intros.
  induction regs; simpl; auto;
    simpl in H.
  erewrite IHregs; intuition.
  induction upds; simpl; auto; f_equal;
    case_eq (fst a =? name); auto;
      intro;
      intuition;
      epose (String.eqb_eq (fst a) name);
      destruct i;
      specialize (H3 H2);
      intuition.
Qed.
    
Lemma NoDupMapFstGetKindAttr: forall (r: RegsT), NoDup (map fst r) <-> NoDup (map fst (getKindAttr r)).
Proof.
  intros; split; intro; [rewrite fst_getKindAttr| rewrite <- fst_getKindAttr]; assumption.
Qed.
