Require Import Kami.All.
Require Import StdLibKami.Arbiter.Impl.
Require Import StdLibKami.FreeList.Spec.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.Arbiter.AuxLemmas.
Require Import StdLibKami.Arbiter.AuxLtac.
Require Import StdLibKami.FreeList.Ifc.
Require Import Coq.Logic.EqdepFacts.
Require Import StdLibKami.KamiCorrectness.

Lemma inversionSemAction'
      k o a reads news calls retC
      (evalA: @SemAction o k a reads news calls retC):
  match a with
  | MCall m s e c =>
    exists mret pcalls,
    SemAction o (c mret) reads news pcalls retC /\
    calls = (m, (existT _ _ (evalExpr e, mret))) :: pcalls
  | LetExpr _ e cont =>
    SemAction o (cont (evalExpr e)) reads news calls retC
  | LetAction _ a cont =>
    exists reads1 news1 calls1 reads2 news2 calls2 r1,
    DisjKey news1 news2 /\
    SemAction o a reads1 news1 calls1 r1 /\
    SemAction o (cont r1) reads2 news2 calls2 retC /\
    reads = reads1 ++ reads2 /\
    news = news1 ++ news2 /\
    calls = calls1 ++ calls2
  | ReadNondet k c =>
    exists rv,
    SemAction o (c rv) reads news calls retC
  | ReadReg r k c =>
    exists rv reads2,
    In (r, existT _ k rv) o /\
    SemAction o (c rv) reads2 news calls retC /\
    reads = (r, existT _ k rv) :: reads2
  | WriteReg r k e a =>
    exists pnews,
    In (r, k) (getKindAttr o) /\
    key_not_In r pnews /\
    SemAction o a reads pnews calls retC /\
    news = (r, (existT _ _ (evalExpr e))) :: pnews
  | IfElse p _ aT aF c =>
    match evalExpr p with
    | true =>
      exists r1,
      r1 = retC /\
      SemAction o (LetAction aT c) reads news calls r1
    | false =>
      exists r1,
      r1 = retC /\
      SemAction o (LetAction aF c) reads news calls retC
    end
  | Sys _ c =>
    SemAction o c reads news calls retC
  | Return e =>
    retC = evalExpr e /\
    news = nil /\
    calls = nil /\
    reads = nil
  end.
Proof.
  destruct evalA; eauto; repeat eexists; try destruct (evalExpr p); eauto; try discriminate; eexists; split; econstructor; eauto.
Qed.

Record FreeListCorrect {len} (imp spec: @FreeList len): Type :=
  {
    freeListRegs: list (Attribute FullKind);
    freeListR: RegsT -> RegsT -> Prop;
    nextToAllocCorrect: EffectlessRelation freeListR (@nextToAlloc _ imp type) (@nextToAlloc _ spec type);
    nextToAllocWb: ActionWb freeListRegs (@nextToAlloc _ imp type);
    allocCorrect: forall allocand, EffectfulRelation freeListR (@alloc _ imp type allocand) (@alloc _ spec type allocand);
    allocWb: forall allocand, ActionWb freeListRegs (@alloc _ imp type allocand);
    freeCorrect: forall input, EffectfulRelation freeListR (@free _ imp type input) (@free _ spec type input);
    freeWb: forall input, ActionWb freeListRegs (@free _ imp type input);
  }.

Record ArbiterCorrect `{ArbiterParams} (imp spec: Arbiter): Type :=
  {
    arbiterRegs: list (Attribute FullKind);
    outerRegs : list (Attribute FullKind);
    arbiterR: RegsT -> RegsT -> Prop;
    sendReqCorrect: forall 
        (req : forall ty : Kind -> Type, ty ArbiterRouterReq -> ActionT ty ArbiterImmRes),
        (forall reqa, ActionWb outerRegs (@req type reqa)) ->
        forall is_err cid creqa , EffectfulRelation arbiterR (@sendReq _ imp is_err req cid type creqa) (@sendReq _ spec is_err req cid type creqa);
    sendReqWb: forall is_err req cid creqa, ActionWb arbiterRegs (@sendReq _ imp is_err req cid type creqa);
    memCallbackCorrect: forall resp, EffectfulRelation arbiterR (@memCallback _ imp type resp) (@memCallback _ spec type resp);
    memCallbackWb: forall resp, ActionWb arbiterRegs (@memCallback _ imp type resp);
    ruleCorrect: EffectfulRelation arbiterR (@arbiterRule _ imp type) (@arbiterRule _ spec type);
    ruleWb: ActionWb arbiterRegs (@arbiterRule _ imp type);
  }.

Section Proofs.
  (** * Common parameters *)
  Context `{A: ArbiterParams}.
  (*
  Context (memReq: forall ty, ty MemReq -> ActionT ty Bool).
  *)
  (** * Spec parameters *)
  Variable (ArrayName ArbiterName AlistName AlistRead AlistWrite : string).
  
(*  Definition specFreeListParams: FreeListParams := Build_FreeListParams transactionTagSz ArrayName.
  Definition specFreeList := (@specFreeList specFreeListParams).*)
  Variable (specFreeList implFreeList: @FreeList numTransactions).
  Variable (implFreeListCorrect: FreeListCorrect implFreeList specFreeList).
  Variable (outerRegs : list (Attribute FullKind)).
  Definition specParams: ArbiterImplParams := 
    {| Arbiter.Impl.arbiter := ArbiterName;
       Arbiter.Impl.alistName := AlistName;
       Arbiter.Impl.alistRead := AlistRead;
       Arbiter.Impl.alistWrite := AlistWrite;
       Arbiter.Impl.freelist := specFreeList |}.
  
  (** * Impl parameters *)
  Definition implParams: ArbiterImplParams :=
    {| Arbiter.Impl.arbiter := ArbiterName;
       Arbiter.Impl.alistName := AlistName;
       Arbiter.Impl.alistRead := AlistRead;
       Arbiter.Impl.alistWrite := AlistWrite;
       Arbiter.Impl.freelist := implFreeList |}.

  (** * The arbiter pseudo-modules involved in the correctness proof *)
  Definition specArbiter := @arbiterImpl A specParams.
  Definition implArbiter := @arbiterImpl A implParams.
  

  Record myArbiterR (freelistR: RegsT -> RegsT -> Prop) freelistRegs outerRegs (o_i o_s: RegsT): Prop :=
    {
      ArbiterVal: bool;
      LocalReg: RegT;
      OuterRegs: RegsT;
      LocalRegVal : LocalReg = (ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal);
      FreeListImplRegs: RegsT;
      FreeListSpecRegs: RegsT;
      HImplRegs: (getKindAttr FreeListImplRegs) = freelistRegs;
      HOuterRegs: (getKindAttr OuterRegs) = outerRegs;
      Ho_iCorrect: o_i = LocalReg :: FreeListImplRegs ++ OuterRegs;
      Ho_sCorrect: o_s = LocalReg :: FreeListSpecRegs ++ OuterRegs;
      Ho_iNoDup: List.NoDup (map fst o_i);
      Ho_sNoDup: List.NoDup (map fst o_s);
      HFreeList: freelistR FreeListImplRegs FreeListSpecRegs
    }.



  
  (* A variant of clean_hyp_step that, among other things, avoids
     applying inversion_sem_action to a few manually specified opaque
     actions. *)
  Ltac mychs :=
    (repeat match goal with
            | _ => mySubst
            | _ => (repeat match goal with
                           | [H: SemAction _ (Impl.alloc _) _ _ _ _ |- _] => revert H
                           | [H: SemAction _ (alloc implFreeList _) _ _ _ _ |- _] => revert H
                           | [H: SemAction _ (Impl.nextToAlloc) _ _ _ _ |- _] => revert H
                           | [H: SemAction _ (nextToAlloc implFreeList) _ _ _ _ |- _] => revert H
                           | [H: SemAction _ (Impl.free _) _ _ _ _ |- _] => revert H
                           | [H: SemAction _ (sendReq _) _ _ _ _ |- _] => revert H
                           end); progress clean_hyp_step
            | [H: match _ with _ => _ end |- _ ] => progress simpl in H
            end); intros.

  (* Used in destSolve, shouldn't be called explicitly *)
  Ltac corSolve HSubmodR SubmodImplRegs :=
    solve[
        first [eapply HSubmodR |
               match goal with
               | [H: (_ = _) \/ In _ _ |- _] =>
                 destruct H;
                 [> mychs;
                  expand_semaction; finisher;
                  solve[discharge_SubList SubmodImplRegs || solve_leftover_Ins SubmodImplRegs]
                 | solve_leftover_Ins SubmodImplRegs]
               end]].

  (* Used in destSolve, shouldn't be called explicitly *)
  Ltac corSolve' SubmodImplRegs :=
    mychs; expand_semaction; discharge_SubList SubmodImplRegs || finisher.

  (* A tactic that could be inlined into new_use_correct but is left as
   its own definition for legibility: This tactic destructs the
   various correctness hypotheses for a given action and solves the
   premises of the correctness hypotheses. *)
  (* Solves SemAction goals that require SemActionExpandRegs--these
   goals can't be solved in general by discharge_SemAction. *)
  (* Used in new_use_correct; shouldn't need to call explicitly *)
  Ltac destSolve HactWb HactCorrect HSubmodR SubmodImplRegs :=
    let HSemGood := fresh "SemActionGood" in
    edestruct HactWb as [HSemGood];
    edestruct HSemGood; finisher;
    edestruct HactCorrect;
    try corSolve HSubmodR SubmodImplRegs;
    try corSolve' SubmodImplRegs.

  (* Takes in an "implementation" action, a hypothesis about the RegsT
   relation associated with its "module", and the "implementation"
   registers associated with its module. This tactic will do as much
   as possible to make use of any correctness hypotheses related to
   this action, adding the information it is able to derive to the
   proof context. This tactic guarantees that it will solve all goals
   raised by destructing the correctness hypotheses; i.e., no new
   obligations will be raised for downstream solving. *)
  (* Simplifies ActionWb, EffectfulRelation, and EffectlessRelation
     hypotheses. *)
  Ltac use_correct act HSubmodR SubmodImplRegs :=
    match goal with
    (* Note that it's not sufficient to match on hypotheses of type
       ActionWb...; some actions take arguments and as such their Wb
       proofs will have binders in their type. *)
    | [HactWb: ?wbT |- _] =>
      lazymatch wbT with
      | context[ActionWb _ _ ?act']  =>
        lazymatch act' with
        | context[act] =>
          match goal with
          (* See above comment about binders which applies here as well. *)
          | [HactCorrect: ?corT |- _] =>
            match corT with
            | context[EffectlessRelation _ ?act'' _] =>
              lazymatch act'' with
              | context[act] =>
                progress noExtraGoals ltac:(destSolve HactWb HactCorrect HSubmodR SubmodImplRegs)
              end
            | context [EffectfulRelation _ ?act'' _] =>
              lazymatch act'' with
              | context[act] =>
                progress noExtraGoals ltac:(destSolve HactWb HactCorrect HSubmodR SubmodImplRegs)
              end
            end
          end
        end
      end
    end.
             

  Lemma SemActionExpand o o' {k} {a : ActionT type k} {reads upds calls ret}:
        forall 
          (HSubList : SubList o o')
          (HSemAction : SemAction o a reads upds calls ret),
          SemAction o' a reads upds calls ret.
  Proof.
    revert reads upds calls ret.
    induction a; intros; try (apply inversionSemAction in HSemAction); dest; subst.
    7 : { destruct (evalExpr e) eqn:G; dest; [econstructor 7 | econstructor 8]; eauto. }
    all : econstructor; eauto.
    rewrite in_map_iff in H; dest.
    specialize (HSubList _ H2).
    rewrite in_map_iff.
    exists x0; split; auto.
  Qed.
  
  Lemma SubList_chain {B C : Type} (l1 : list (B * C)):
    forall (l2 l3 : list (B * C))
           (HNoDup : NoDup (map fst l2))
           (HSubList1 : SubList l1 l2)
           (HSubList2 : SubList l3 l2)
           (HKeysMatch : map fst l1 = map fst l3),
      l1 = l3.
  Proof.
    induction l1; intros.
    - destruct l3; inv HKeysMatch; auto.
    - destruct a; simpl in *.
      destruct l3; inversion HKeysMatch.
      destruct p; simpl in *; subst.
      rewrite (NoDup_map_fst HNoDup (HSubList1 _ (in_eq _ _)) (HSubList2 _ (in_eq _ _))) in *.
      erewrite IHl1; eauto; eapply SubList_cons; eauto.
  Qed.


  Lemma app_cons :
    (forall (A : Type) (a : A) (l : list A),
        a :: l = [a] ++ l).
  Proof.
    auto.
  Qed.
  
  (* Pretty stupid, but it works for now *)
  Ltac prove_sublist :=
    match goal with
    | |- SubList ?l1 ?l2 => clear; repeat intro; repeat (simpl in *; rewrite in_app_iff in *); firstorder fail
    end.

  (* prototype for dealing with special relational actions *)
  Ltac resolve_rel :=
    let o_j := fresh "o_j" in
    let HSL1 := fresh "HSL1" in
    let HSL2 := fresh "HSL2" in
    let HCorrect := fresh "HCorrect" in
    let HSemAction := fresh "HSemAction" in
    let HR := fresh "HR" in
    let TMP := fresh "TMP" in
    let HSemAction_s := fresh "HSemAction_s" in
    let HupdsNil := fresh "HupdsNil" in
    let HcallsNil := fresh "HcallsNil" in
    let reads_s := fresh "reads_s" in
    let upds_s := fresh "upds_s" in                                                           
    match goal with
    | [HSemAction1 : SemAction ?o_i ?a_i ?reads ?upds ?calls ?retV,
       HActionWb : ActionWb (getKindAttr ?o_i1) ?a_i,
       Ho_iNoDup : NoDup (map fst ?o_i) |- exists _ _, (SemAction ?o_s _ _ _ _ _ /\ _)] =>
      specialize (HActionWb _ _ _ _ _ HSemAction1) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]
      ; assert (SubList o_i1 o_i) as TMP
      ; [prove_sublist
        |rewrite (SubList_chain Ho_iNoDup HSL1 TMP (getKindAttr_fst _ _ HCorrect)) in HSemAction; clear TMP]
      ; match goal with
        | [HERelation : EffectlessRelation ?R a_i _,
                        HoRelation : ?R o_i1 ?o_j1 |- _] =>
          idtac "hyp1 found"
          ; specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
          ; assert (SubList o_j1 o_s) as TMP
        | [HERelation : EffectfulRelation ?R a_i _,
                        HoRelation : ?R o_i1 ?o_j1 |- _] =>
          idtac "hyp2 found"
          ; specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction) as [reads_s [upds_s [HSemAction_s HdoUpdRegsR]]]
          ; assert (SubList o_j1 o_s) as TMP
        | _ => idtac "default 1 found"
               ; rename HSemAction into HSemAction_s
               ; assert (SubList o_i1 o_s) as TMP
        end
      ; [prove_sublist
        | apply (SemActionExpand TMP) in HSemAction_s; clear TMP]
    | [HSemAction1 : SemAction ?o_i (?a_i _) ?reads ?upds ?calls ?retV,
       HActionWb : forall _, ActionWb (getKindAttr ?o_i1) (?a_i _),
       Ho_iNoDup : NoDup (map fst ?o_i) |- exists _ _, (SemAction ?o_s _ _ _ _ _ /\ _)] =>
      idtac "Attempt : specialize (" HActionWb " _ _ _ _ _ _ " HSemAction1 ") as [["o_j" ["HSL1" ["HSL2" ["HCorrect" "HSemAction"]]]] "HR"]"
      ; specialize (HActionWb _ _ _ _ _ _ HSemAction1) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]
      ; assert (SubList o_i1 o_i) as TMP
      ; [prove_sublist
        |rewrite (SubList_chain Ho_iNoDup HSL1 TMP (getKindAttr_fst _ _ HCorrect)) in HSemAction; clear TMP]
      ; match goal with
        | [HERelation : forall _, EffectlessRelation ?R (a_i _) _,
             HoRelation : ?R o_i1 ?o_j1 |- _] =>
          idtac "hyp1.2 found"     
          ; specialize (HERelation _ _ _ HoRelation _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
          ; assert (SubList o_j1 o_s) as TMP
        | [HERelation : forall _, EffectfulRelation ?R (a_i _) _,
             HoRelation : ?R o_i1 ?o_j1 |- _] =>
          idtac "hyp2.2 found"
          ; idtac "Attempt : specialize (" HERelation " _ _ _ " HoRelation " _ _ _ _ " HSemAction ")"
          ; specialize (HERelation _ _ _ HoRelation _ _ _ _ HSemAction) as [reads_s [upds_s [HSemAction_s HdoUpdRegsR]]]
          ; assert (SubList o_j1 o_s) as TMP
        | _ => idtac "default 1.2 found"
               ; rename HSemAction into HSemAction_s
               ; assert (SubList o_i1 o_s) as TMP
        end
      ; [prove_sublist
        |apply (SemActionExpand TMP) in HSemAction_s; clear TMP]
    | _ => idtac "external hyp not matched"                  
    end.

  Ltac resolve_wb :=
    match goal with
    | [HSemAction : SemAction ?o1 ?a_i _ _ _ _,
       HActionWb : ActionWb (getKindAttr ?o2) ?a_i |- _] =>
      specialize (HActionWb _ _ _ _ _ HSemAction) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]
    | [HSemAction : SemAction _ (?a_i _) _ _ _ _,
       HActionWb : forall _, ActionWb _ (?a_i _) |- _] =>
      specialize (HActionWb _ _ _ _ _ _ HSemAction) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]
    end.

  Lemma NoDup_app_Disj_iff {B : Type} (eqDec : forall a1 a2 : B, {a1 = a2} + {a1 <> a2}):
  forall (l1 l2 : list B),
    NoDup (l1 ++ l2) <-> NoDup l1 /\ NoDup l2 /\ (forall a : B, ~In a l1 \/ ~In a l2).
  Proof.
    red; repeat split; intros; dest.
    rewrite NoDup_app_iff in H; dest; auto.
    rewrite NoDup_app_iff in H; dest; auto.
    apply NoDup_app_Disj; auto.
    rewrite NoDup_app_iff; repeat split; auto; intros.
    destruct (in_dec eqDec a l2); eauto.
    destruct (H1 a); eauto.
    destruct (in_dec eqDec a l1); eauto.
    destruct (H1 a); eauto.
  Qed.

  Corollary NoDup_app_DisjKey {B : Type} :
    forall (l1 l2 : list (string * B)),
      NoDup (map fst (l1 ++ l2)) <-> NoDup (map fst l1) /\ NoDup (map fst l2) /\ DisjKey l1 l2.
  Proof.
    intros; rewrite map_app, NoDup_app_Disj_iff; unfold DisjKey;[reflexivity|apply string_dec].
  Qed.

  Lemma DisjKey_app_split_r {B C : Type} :
    forall (l1 l2 l3 : list (B * C)),
      DisjKey l1 (l2 ++ l3) <-> DisjKey l1 l2 /\ DisjKey l1 l3.
  Proof.
    split; intros.
    - split; intro k; specialize (H k); rewrite map_app, in_app_iff, DeM1 in H; destruct H; dest; auto.
    - dest; intro.
      destruct (H k); destruct (H0 k); rewrite map_app, in_app_iff, DeM1; auto.
  Qed.

  Corollary DisjKey_app_split_l {B C : Type} :
    forall (l1 l2 l3 : list (B * C)),
      DisjKey (l1 ++ l2) l3 <-> DisjKey l1 l3 /\ DisjKey l2 l3.
  Proof.
    split; intros.
    - apply DisjKey_Commutative in H; rewrite DisjKey_app_split_r in H; dest; eauto using DisjKey_Commutative.
    - apply DisjKey_Commutative; rewrite DisjKey_app_split_r; dest; eauto using DisjKey_Commutative.
  Qed.

  Lemma NoDup_singleton_map {B C : Type}:
    forall (a : B) (f : B -> C),
      NoDup (map f [a]) <-> True.
  Proof.
    intros; repeat constructor; auto.
  Qed.

  Lemma DisjKey_singletons {B : Type} :
        forall (a b : string * B),
          DisjKey [a] [b] <-> fst a <> fst b.
  Proof.
    unfold DisjKey; split; repeat intro; simpl in *.
    - rewrite H0 in H; destruct (H (fst b)); auto.
    - destruct (string_dec k (fst b)); subst.
      + left; intro G; destruct G; auto.
      + right; intro G; destruct G; auto.
  Qed.

  Lemma DisjKey_singleton_l {B : Type} :
    forall (a : string * B) (l : list (string * B)),
      DisjKey [a] l <-> key_not_In (fst a) l.
  Proof.
    unfold DisjKey, key_not_In; split; simpl; repeat intro.
    - apply (in_map fst) in H0; simpl in *.
      specialize (H (fst a)); destruct H; auto.
    - destruct (string_dec k (fst a)); subst.
      + right; intro.
        rewrite in_map_iff in H0; dest; destruct x; simpl in *; subst.
        specialize (H b); contradiction.
      + left; intro; destruct H0; auto.
  Qed.


  Corollary DisjKey_singleton_r {B : Type} :
    forall (a : string * B) (l : list (string * B)),
      DisjKey l [a] <-> key_not_In (fst a) l.
  Proof.
    split; intro.
    - apply DisjKey_Commutative in H; rewrite DisjKey_singleton_l in H; assumption.
    - apply DisjKey_Commutative; rewrite DisjKey_singleton_l; assumption.
  Qed.
  
  Lemma key_not_In_cons {B C : Type} :
    forall (a : B) (b : B * C) (l : list (B * C)),
      key_not_In a (b :: l) <->  a <> fst b /\ key_not_In a l.
  Proof.
    split; intros; rewrite app_cons in *; [rewrite key_not_In_app_iff in H| rewrite key_not_In_app_iff]; dest; split; auto.
    - intro; destruct b; simpl in *; subst; eapply H; simpl; auto.
    - repeat intro; destruct b; simpl in *; subst; destruct H1; auto.
      apply inversionPair in H1; dest; subst; apply H; reflexivity.
  Qed.

  Lemma DisjKey_cons_l {B C : Type} (Heq_dec : forall (a b : B), {a = b} + {a <> b}):
    forall (b : B * C) (l1 l2 : list (B * C)),
      DisjKey (b :: l1) l2 <-> key_not_In (fst b) l2 /\ DisjKey l1 l2.
  Proof.
    repeat split; intros; dest.
    - specialize (H (fst b)); destruct H; rewrite key_not_In_fst; simpl in *; auto.
    - rewrite app_cons in H.
      rewrite DisjKey_app_split_l in H; dest; auto.
    - rewrite app_cons, DisjKey_app_split_l; split; auto.
      repeat intro.
      rewrite key_not_In_fst in H.
      destruct (Heq_dec k (fst b)); subst; simpl; auto.
      left; intro; destruct H1; auto.
  Qed.

  Corollary DisjKey_cons_l_str {B : Type} :
    forall (b : string * B) (l1 l2 : list (string * B)),
      DisjKey (b :: l1) l2 <-> key_not_In (fst b) l2 /\ DisjKey l1 l2.
  Proof. intros; apply (DisjKey_cons_l string_dec). Qed.

  Corollary DisjKey_cons_r_str {B : Type} :
    forall (b : string * B) (l1 l2 : list (string * B)),
      DisjKey l1 (b :: l2) <-> key_not_In (fst b) l1 /\ DisjKey l1 l2.
  Proof.
    split; intros; [ apply DisjKey_Commutative in H; rewrite DisjKey_cons_l_str in H
                   | apply DisjKey_Commutative; rewrite DisjKey_cons_l_str]
    ; dest; split; auto; apply DisjKey_Commutative; assumption.
  Qed.
  
  (* Attempts to normalize (NoDup fst _) type goals *)
  (* NoDup (map fst (a :: l1 ++ l2)) => True /\ (NoDup (map fst l1) /\ NoDup (map fst l2) /\ DisjKey l1 l2) /\ key_not_In (fst a) l1 /\ key_not_In (fst a) l2 *)
(*
  Ltac simpl_nodup_map_fst :=
    match goal with
    | [ |- context [NoDup (map fst (?a :: nil))]] => rewrite (NoDup_singleton_map a fst)
    | [ |- context [DisjKey (?a :: nil ) (?b :: nil)]] => rewrite (DisjKey_singletons a b)
    | [ |- context [NoDup (map fst (_ ++ _))]] => rewrite NoDup_app_DisjKey
    | [ |- context [NoDup (map fst (_ :: _))]] => rewrite app_cons, NoDup_app_DisjKey
    | [ |- context [DisjKey (_ ++ _) _]] => rewrite DisjKey_app_split_l
    | [ |- context [DisjKey _ (_ ++ _)]] => rewrite DisjKey_app_split_r
    | [ |- context [DisjKey (?a :: nil ) ?l]] => rewrite (DisjKey_singleton_l a l)
    | [ |- context [DisjKey ?l (?a :: nil )]] => rewrite (DisjKey_singleton_r a l)
    | [ |- context [DisjKey _ (_ :: _)]] => rewrite app_cons, DisjKey_app_split_r
    | [ |- context [DisjKey (_ :: _) _]] => rewrite app_cons, DisjKey_app_split_l
    | [ |- context [key_not_In _ (_ ++ _)]] => rewrite key_not_In_app_iff
    | [ |- context [key_not_In _ (_ :: nil)]] => rewrite key_not_In_singleton
    | [ |- context [key_not_In _ (_ :: _)]] => rewrite app_cons, key_not_In_app_iff
    end.
*)
                                         
  
  Lemma map_nil {B C : Type} {f : B -> C}:
    map f nil = nil.
  Proof. auto. Qed.
  
  Ltac reduce_map :=
    repeat (rewrite map_cons in * || rewrite map_app in * || rewrite map_nil in *).
            
  Ltac decompose_NoDup_string :=
    repeat (rewrite NoDup_cons_iff in * || rewrite (NoDup_app_Disj_iff string_dec) in * || rewrite in_app_iff in * || rewrite DeM1 in *).
  



  Lemma doUpdRegs_app_r o :
    forall u o', 
      doUpdRegs u (o ++ o') = (doUpdRegs u o) ++ (doUpdRegs u o').
  Proof.
    induction o; intros; simpl; auto.
    case_eq (findReg (fst a) u); intros; subst; f_equal; rewrite IHo; auto.
  Qed.

  Lemma findReg_Some_app u :
    forall s u' x,
      findReg s (u ++ u') = Some x ->
      findReg s u  = Some x \/ findReg s u' = Some x.
  Proof.
    induction u; simpl; intros; auto.
    destruct String.eqb eqn:G; auto.
  Qed.

  Lemma findReg_Some_app_ordered u :
    forall s u' x y,
      findReg s (u ++ u') = Some x ->
      findReg s u = Some y ->
      x = y.
  Proof.
    induction u; simpl; intros;[discriminate|].
    destruct String.eqb.
    - rewrite H in H0; inv H0; reflexivity.
    - eapply IHu; eauto.
  Qed.

  Lemma doUpdRegs_l_reduce o :
    forall u u',
      DisjKey u o ->
      doUpdRegs (u ++ u') o = doUpdRegs u' o.
  Proof.
    induction o; simpl; auto; intros.
    destruct (findReg (fst a) (u ++ u')) eqn:G, (findReg (fst a) u') eqn:G0.
    - apply findReg_Some_app in G.
      destruct G.
      + exfalso.
        apply findRegs_Some', (in_map fst) in H0.
        specialize (H (fst a)).
        destruct H; simpl in *; auto.
      + rewrite H0 in G0; inv G0; f_equal; apply IHo.
        intro k; specialize (H k); simpl in H; destruct H; auto.
    - exfalso.
      apply findReg_Some_app in G.
      destruct G;[apply findRegs_Some', (in_map fst) in H0| rewrite H0 in G0; discriminate].
      specialize (H (fst a)).
      destruct H; simpl in *; auto.
    - exfalso.
      rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G; dest.
      apply findRegs_Some', (in_map fst) in G0; auto.
    - rewrite IHo; auto.
      intro k; specialize (H k); simpl in *; destruct H; auto.
  Qed.

  Lemma doUpdRegs_r_reduce o :
    forall u u',
      DisjKey u' o ->
      doUpdRegs (u ++ u') o = doUpdRegs u o.
  Proof.
    induction o; simpl; auto; intros.
    destruct (findReg (fst a) (u ++ u')) eqn:G, (findReg (fst a) u) eqn:G0.
    - apply findReg_Some_app in G.
      destruct G.
      + rewrite H0 in G0; inv G0; f_equal; apply IHo.
        intro k; specialize (H k); simpl in H; destruct H; auto.
      + exfalso.
        apply findRegs_Some', (in_map fst) in H0.
        specialize (H (fst a)).
        destruct H; simpl in *; auto.
    - exfalso.
      apply findReg_Some_app in G.
      destruct G;[rewrite H0 in G0; discriminate| apply findRegs_Some', (in_map fst) in H0].
      specialize (H (fst a)).
      destruct H; simpl in *; auto.
    - exfalso.
      rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G; dest.
      apply findRegs_Some', (in_map fst) in G0; auto.
    - rewrite IHo; auto.
      intro k; specialize (H k); simpl in *; destruct H; auto.
  Qed.

  Lemma doUpdRegs_DisjKey o :
    forall u,
      DisjKey u o ->
      doUpdRegs u o = o.
  Proof.
    induction o; simpl; auto; intros.
    destruct (findReg (fst a) u) eqn:G.
    - exfalso; apply findRegs_Some' in G.
      apply (in_map fst) in G; destruct (H (fst a)); auto.
      apply H0; simpl; auto.
    - rewrite IHo; auto.
      intro k; destruct (H k); simpl in *; auto.
  Qed.
  
  Lemma doUpdRegs_app_l o :
    forall u u',
      doUpdRegs (u ++ u') o = doUpdRegs u (doUpdRegs u' o).
  Proof.
    induction o; simpl; auto; intros.
    destruct (findReg (fst a) (u ++ u')) eqn:G, (findReg (fst a) u') eqn:G0, (findReg (fst a) u) eqn:G1
    ; simpl; try (rewrite G1).
    - f_equal; auto.
      rewrite (findReg_Some_app_ordered _ _ _ G G1); reflexivity.
    - apply findReg_Some_app in G; destruct G as [G|G]; rewrite G in *;[discriminate|inv G0].
      f_equal; eauto.
    - apply findReg_Some_app in G; destruct G as [G|G]; rewrite G in *;[inv G1|discriminate].
      f_equal; eauto.
    - apply findReg_Some_app in G; rewrite G0, G1 in G; destruct G; discriminate.
    - rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G.
      apply findRegs_Some', (in_map fst) in G0; dest; contradiction.
    - rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G.
      apply findRegs_Some', (in_map fst) in G0; dest; contradiction.
    - rewrite <- findRegs_None, map_app, in_app_iff, DeM1 in G.
      apply findRegs_Some', (in_map fst) in G1; dest; contradiction.
    - f_equal; eauto.
  Qed.

  Lemma doUpdRegs_cons_l o :
    forall r u,
      doUpdRegs (r::u) o = doUpdRegs [r] (doUpdRegs u o).
  Proof.
    intros; rewrite app_cons; apply doUpdRegs_app_l.
  Qed.
  
  Ltac find_if_inside :=
    match goal with
    | [H : ?X = _ |- context[if ?X then _ else _] ] => rewrite H
    end.
  
  Lemma doUpdReg_preserves_getKindAttr :
    forall u o,
      NoDup (map fst o) ->
      SubList (getKindAttr u) (getKindAttr o) ->
      getKindAttr (doUpdRegs u o) = getKindAttr o.
  Proof.
    symmetry; erewrite getKindAttr_doUpdRegs; eauto; intros.
    apply H0; rewrite in_map_iff; eexists; split; eauto.
    simpl; reflexivity.
  Qed.

  Lemma doUpdRegs_preserves_keys o :
    forall u,
      map fst (doUpdRegs u o) = map fst o.
  Proof.
    induction o; simpl; auto; intros.
    destruct findReg; rewrite IHo; reflexivity.
  Qed.

  Lemma DisjKey_rewrite_l {B C : Type} :
    forall (l1 l2 l3: list (B * C)),
      map fst l1 = map fst l2 ->
      DisjKey l1 l3 <-> DisjKey l2 l3.
  Proof.
    intros; split; unfold DisjKey; repeat intro; rewrite H in *; auto.
  Qed.

  Lemma doUpdRegs_key_not_In a l1 :
    key_not_In (fst a) l1 ->
    doUpdRegs [a] l1 = l1.
  Proof.
    intro.
    rewrite <- DisjKey_singleton_l in H.
    apply doUpdRegs_DisjKey; assumption.
  Qed.

  Lemma doUpdRegs_keys_neq a b :
    fst a <> fst b ->
    doUpdRegs [a] [b] = [b].
  Proof.
    rewrite <- DisjKey_singletons; intros.
    apply doUpdRegs_DisjKey; assumption.
  Qed.
  
  Lemma in_cons_iff {B : Type} {a b : B} {l : list B}:
    In a (b :: l) <-> b = a \/ In a l.
  Proof.
    split; intros; simpl in *; auto.
  Qed.
  (* Some notes.
     Try to keep the Arbiter actions in lockstep, unraveling twin SemActions together
     After a LetAction or LetExpr, check to see if there is a hypothesis/goal pair matching an Effect(full/less) relation pair, and an ActionWb rule.
     These should be the only places where this is necessary as IfElse statements are transformed into LetActions.
     
     mySubst needs to be more robust, we should be solving as many generic goals as possible here.
     We could probably use some bespoke rules for dealing with each of the generic constructors to make the problem set up more stremlined.

     If you have a SemAction in the goal with a SemAction in the hypothesis that you don't recognize, attempt to unfold them to the same action.
     If they are not an ActionT constructor type after unfolding, then we have to assume they're a relational type.
     Try to find the appropriate ActionWb relation associated with the type in the goal, similarly find the Effect(full/less) relation between the
     goal and one or more actions in the hypothesis.
     Shrink the current SemAction state registers to fit the ActionWb parameter.
     Destruct the appropriate ActionWb hypothesis, use as input to Effect(less/full) relation, destruct said relation, collect witnesses.
     Expand resulting SemAction state registers to fit goal.
     Apply goal, repeat as needed.
   *)
  
  Lemma nIn_app_iff {B : Type} (Heq_dec : forall (a b : B), {a = b} + {a <> b}) :
    forall (a : B) (l1 l2 : list B),
      ~In a (l1 ++ l2) <-> ~In a l1 /\ ~In a l2.
  Proof. split; intros; rewrite in_app_iff, DeM1 in *; auto. Qed.

  Lemma SubList_nil_r {B : Type} :
    forall (l : list B),
      SubList l nil -> l = nil.
  Proof.
    repeat intro; induction l; auto.
    exfalso; specialize (H _ (in_eq _ _)); auto.
  Qed.

  Lemma SubList_filter {B : Type} :
    forall (a : B) (l1 l2 : list B),
      SubList l1 l2 ->
      ~In a l2 ->
      ~In a l1.
  Proof. repeat intro; eauto. Qed.

  Lemma DisjKey_filter {B C : Type} :
    forall (l1 l2 l3 l4 : list (B * C)),
      SubList (map fst l3) (map fst l1) ->
      SubList (map fst l4) (map fst l2) ->
      DisjKey l1 l2 ->
      DisjKey l3 l4.
  Proof. repeat intro; firstorder fail. Qed.

  Lemma DisjKey_filter_r {B C : Type} :
    forall (l1 l2 l3 : list (B * C)),
      SubList (map fst l3) (map fst l2) ->
      DisjKey l1 l2 ->
      DisjKey l1 l3.
  Proof. repeat intros; firstorder fail. Qed.

  Lemma DisjKey_filter_l {B C : Type} :
    forall (l1 l2 l3 : list (B * C)),
      SubList (map fst l3) (map fst l2) ->
      DisjKey l2 l1 ->
      DisjKey l3 l1.
  Proof. repeat intros; firstorder fail. Qed.

  Definition doUpdReg (u : RegsT) (r : RegT) : RegT :=
    match findReg (fst r) u with
    | Some y => (fst r, y)
    | None => r
    end.

  Fixpoint oneUpdRegs (r : RegT) (o : RegsT) : RegsT :=
    match o with
    | nil => nil
    | x :: o'
      => (if String.eqb (fst x) (fst r)
          then r
          else x) :: (oneUpdRegs r o')
    end.

  Definition oneUpdReg (r1 r2 : RegT) : RegT :=
    if String.eqb (fst r2) (fst r1) then r1 else r2.
  
  Lemma doUpdRegs_cons_r' :
    forall (u o : RegsT) (r : RegT),
      doUpdRegs u (r :: o) = doUpdReg u r :: doUpdRegs u o.
  Proof. intros; simpl; auto. Qed.

  Lemma oneUpdRegs_doUpdRegs :
    forall (o : RegsT) (r : RegT),
      doUpdRegs [r] o = oneUpdRegs r o.
  Proof.
    induction o; intros; auto.
    simpl; destruct String.eqb eqn:G; f_equal; eauto.
    rewrite String.eqb_eq in G; rewrite G; destruct r; reflexivity.
  Qed.


  Lemma doUpdRegs_cons_l' :
    forall (u o : RegsT) (r : RegT),
      doUpdRegs (r :: u) o = oneUpdRegs r (doUpdRegs u o).
  Proof.
    intros.
    rewrite <- oneUpdRegs_doUpdRegs, doUpdRegs_cons_l; reflexivity.
  Qed.
  
  Lemma doUpdReg_oneUpdReg :
    forall (r1 r2 : RegT),
      oneUpdReg r1 r2 = doUpdReg [r1] r2.
  Proof.
    intros; unfold oneUpdReg, doUpdReg, findReg.
    destruct String.eqb eqn:G; auto.
    rewrite String.eqb_eq in G; rewrite G; destruct r1; reflexivity.
  Qed.
  
  Lemma oneUpdRegs_cons :
    forall (o : RegsT) (r1 r2 : RegT),
      oneUpdRegs r1 (r2 :: o) = oneUpdReg r1 r2 :: oneUpdRegs r1 o.
  Proof.
    intros; rewrite <- oneUpdRegs_doUpdRegs, doUpdRegs_cons_r', <- doUpdReg_oneUpdReg.
    f_equal; apply oneUpdRegs_doUpdRegs.
  Qed.

  Lemma oneUpdRegs_app :
    forall (o1 o2 : RegsT) (r : RegT),
      oneUpdRegs r (o1 ++ o2) = oneUpdRegs r o1 ++ oneUpdRegs r o2.
  Proof.
    intros; repeat rewrite <- oneUpdRegs_doUpdRegs; rewrite doUpdRegs_app_r; reflexivity.
    Qed.
  
  Lemma doUpdReg_doUpdRegs :
    forall (u : RegsT) (r : RegT),
      doUpdRegs u [r] = [doUpdReg u r].
  Proof. auto. Qed.
  
  Lemma doUpdReg_app :
    forall (u1 u2 : RegsT) (r : RegT),
      doUpdReg (u1 ++ u2) r = doUpdReg u1 (doUpdReg u2 r).
  Proof.
    intros.
    enough ([doUpdReg (u1 ++ u2) r] = [doUpdReg u1 (doUpdReg u2 r)]) as P.
    { inv P; reflexivity. }
    repeat rewrite <- doUpdReg_doUpdRegs; rewrite doUpdRegs_app_l; reflexivity.
  Qed.

  Lemma doUpdReg_cons :
    forall (u : RegsT) (r1 r2 : RegT),
      doUpdReg (r1 :: u) r2 = oneUpdReg r1 (doUpdReg u r2).
  Proof.
    intros.
    enough ([doUpdReg (r1 :: u) r2] = [oneUpdReg r1 (doUpdReg u r2)]) as P.
    { inv P; reflexivity. }
    rewrite <- doUpdReg_doUpdRegs, doUpdRegs_cons_l, doUpdReg_doUpdRegs, oneUpdRegs_doUpdRegs.
    reflexivity.
  Qed.

  Lemma doUpdReg_notIn :
    forall  (u : RegsT) (r : RegT),
      ~ In (fst r) (map fst u) ->
      doUpdReg u r = r.
  Proof.
    induction u; intros; auto.
    unfold doUpdReg; destruct findReg eqn:G; auto.
    exfalso; apply findRegs_Some', (in_map fst) in G; apply H; assumption.
  Qed.

  Corollary doUpdReg_nil :
    forall (r : RegT),
      doUpdReg nil r = r.
  Proof. eauto using in_nil, doUpdReg_notIn. Qed.

  Lemma oneUpdRegs_notIn :
    forall (u : RegsT) (r : RegT),
      ~ In (fst r) (map fst u) ->
      oneUpdRegs r u = u.
  Proof.
    induction u; intros; auto.
    simpl; destruct String.eqb eqn:G.
    - rewrite String.eqb_eq in G; simpl in H; subst.
      exfalso; apply H; auto.
    - f_equal; apply IHu; intro; apply H; simpl; auto.
  Qed.

  Lemma DisjKey_rewrite_r {B C : Type}:
    forall (l1 l2 l3 : list (B * C)),
      map fst l1 = map fst l2 ->
      DisjKey l3 l1 <->
      DisjKey l3 l2.
  Proof.
    split; intros; apply DisjKey_Commutative.
    - rewrite DisjKey_rewrite_l; [apply (DisjKey_Commutative H0)| apply eq_sym, H].
    - rewrite DisjKey_rewrite_l; [apply (DisjKey_Commutative H0)| apply H].
  Qed.

  Ltac clean_useless_hyp :=
    match goal with
    | [ H : ?a = ?a |- _] => clear H
    | [ H : True |- _] => clear H
    | [ H : SubList nil _ |- _] => clear H
    | [ H : key_not_In _ nil |- _] => clear H
    | [ H : DisjKey _ nil |- _] => clear H
    | [ H : DisjKey nil _ |- _] => clear H
    | [ H : NoDup nil |- _] => clear H
    | [ H : NoDup (_ :: nil) |- _] => clear H
    | [ H : ~In _ nil |- _] => clear H
    end.

  Ltac normalize_key_hyps :=
    match goal with
    | [ H : key_not_In _ (_ ++ _) |- _] => rewrite key_not_In_app_iff in H; destruct H as [? ?]
    | [ H : key_not_In _ (_ :: _) |- _] => rewrite key_not_In_cons in H; destruct H as [? ?]
    | [ H : key_not_In _ _ |- _] => rewrite key_not_In_fst in H
    | [ H : DisjKey (_ ++ _) _ |- _] => rewrite DisjKey_app_split_l in H; destruct H as [? ?]
    | [ H : DisjKey _ (_ ++ _) |- _] => rewrite DisjKey_app_split_r in H; destruct H as [? ?]
    | [ H : DisjKey (_ :: _) _ |- _] => rewrite DisjKey_cons_l_str in H; destruct H as [? ?]
    | [ H : DisjKey _ (_ :: _) |- _] => rewrite DisjKey_cons_r_str in H; destruct H as [? ?]
    | [ H : NoDup (_ :: _) |- _] => rewrite NoDup_cons_iff in H; destruct H as [? ?]
    | [ H : NoDup (_ ++ _) |- _] => rewrite (NoDup_app_Disj_iff string_dec) in H; destruct H as [? [? ?]]
    | [ H : ~In _ (_ :: _) |- _] => rewrite not_in_cons in H; destruct H as [? ?]
    | [ H : ~In _ (_ ++ _) |- _] => rewrite (nIn_app_iff string_dec) in H; destruct H as [? ?]
    end.

  Ltac normalize_key_concl :=
    match goal with
    | [ |- key_not_In _ (_ ++ _)] => rewrite key_not_In_app_iff; split
    | [ |- key_not_In _ (_ :: _)] => rewrite key_not_In_cons; split
    | [ |- key_not_In _ _] => rewrite key_not_In_fst
    | [ |- DisjKey (_ ++ _) _] => rewrite DisjKey_app_split_l; split
    | [ |- DisjKey _ (_ ++ _)] => rewrite DisjKey_app_split_r; split
    | [ |- DisjKey (_ :: _) _] => rewrite DisjKey_cons_l_str; split
    | [ |- DisjKey _ (_ :: _)] => rewrite DisjKey_cons_r_str; split
    | [ |- NoDup (_ :: _)] => rewrite NoDup_cons_iff; split
    | [ |- NoDup (_ ++ _)] => rewrite (NoDup_app_Disj_iff string_dec); repeat split
    | [ |- ~In _ (_ :: _)] => rewrite not_in_cons; split
    | [ |- ~In _ (_ ++ _)] => rewrite (nIn_app_iff string_dec); split
    end.
  
  Ltac my_simplifier :=
    match goal with
    | [ H : context [map _ nil] |- _] => idtac "m_s 1"; rewrite map_nil in H
    | [ H : context [map _ (_ ++ _)] |- _] => idtac "m_s 2"; rewrite map_app in H
    | [ H : context [map _ (_ :: _)] |- _] => idtac "m_s 3"; rewrite map_cons in H
    | [ H : _ \/ _ |- _] => idtac "or"; destruct H
    | [ H : _ /\ _ |- _] => idtac "and"; destruct H
    | [ H : SubList _ nil |- _] => idtac "SubList right nil"; apply SubList_nil_r in H
    | [ H : (_, _) = (_, _) |- _] => idtac "pair_eq"; apply inversionPair in H; destruct H as [? ?]
    | [ H : existT ?a ?b ?c1 = existT ?a ?b ?c2 |- _] => idtac "EqDep1"; apply Eqdep.EqdepTheory.inj_pair2 in H
    | [ H : existT ?a ?b1 ?c1 = existT ?a ?b2 ?c2 |- _] => idtac "EqDep2"; apply inversionExistT in H; destruct H as [? ?]
    | [ H1 : In (?a, ?b) ?c, H2 : ~In ?a (map fst ?c) |- _] => idtac "In nIn fst H1 := "H1": In ("a","b") "c" H2 := " H2; apply (in_map fst) in H1; contradiction
    | [ H : forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2)) |- _] => fold (DisjKey l1 l2) in H
    | [ |- context [map _ nil]] => idtac "m_s 4"; rewrite map_nil
    | [ |- context [map _ (_ ++ _)]] => idtac "m_s 5"; rewrite map_app
    | [ |- context [map _ (_ :: _)]] => idtac "m_s 6"; rewrite map_cons
    | [ |- context [In _ (_ :: _)]] => idtac "in_cons_iff concl"; rewrite in_cons_iff
    | [ |- context [In _ (_ ++ _)]] => idtac "in_app_iff concl"; rewrite in_app_iff
    end.

  Ltac my_simpl_solver :=
    match goal with
    | [ |- DisjKey nil _] => apply DisjKey_nil_l
    | [ |- DisjKey _ nil] => apply DisjKey_nil_r
    | [ |- ?a = ?a] => reflexivity
    | [ |- True] => apply I
    | [ |- NoDup nil] => constructor
    | [ |- ~In _ nil] => intro; my_simpl_solver
    | [ |- NoDup (_ :: nil)] => econstructor; my_simpl_solver
    | [ H : False |- _] => idtac "False"; exfalso; apply H
    | [ H : ?a <> ?a |- _] => idtac "neq"; exfalso; apply H; reflexivity
    | [ H : In _ nil |- _] => idtac "In nil"; inversion H
    end.
  
  Ltac decompose_In H :=
    repeat (rewrite in_cons_iff in H || rewrite in_app_iff in H).
  
  Ltac resolve_wb' :=
    let o_j := fresh "o" in
    let HSL1 := fresh "H" in
    let HSL2 := fresh "H" in
    let HCorrect := fresh "H" in
    let HSemAction := fresh "H" in
    let HR := fresh "H" in
    match goal with
    | [HSemAction1 : SemAction ?o1 ?a_i _ _ _ _,
                     HActionWb : ActionWb (getKindAttr ?o2) ?a_i |- _] =>
      specialize (HActionWb _ _ _ _ _ HSemAction1) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]; clear HSemAction1
    | [HSemAction1 : SemAction _ (?a_i _) _ _ _ _,
                     HActionWb : forall _, ActionWb _ (?a_i _) |- _] =>
      specialize (HActionWb _ _ _ _ _ _ HSemAction1) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]; clear HSemAction1
    end.

  Ltac resolve_rel' :=
    let HupdsNil := fresh "HupdsNil" in
    let HcallsNil := fresh "HcallsNil" in
    let reads_s := fresh "reads_s" in
    let HSemAction_s := fresh "HSemAction_s" in
    let upds_s := fresh "upds_s" in
    let HdoUpdRegsR := fresh "HdoUpdRegsR" in
    match goal with
    | [HSemAction : SemAction ?o_i ?a_i _ _ _ _,
                    HERelation : EffectlessRelation ?R ?a_i _,
                                 HoRelation : ?R ?o_i _ |- _] =>
      specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
      ; clear HSemAction
    | [HSemAction : SemAction ?o_i1 (?a_i _) _ _ _ _,
                    HERelation : forall _, EffectlessRelation ?R (?a_i _) _,
         HoRelation : ?R ?o_i2 ?o_j |- _] =>
      specialize (HERelation _ _ _ HoRelation _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
      ; clear HSemAction
    | [HSemAction : SemAction ?o_i1 ?a_i _ _ _ _,
                    HERelation : EffectfulRelation ?R ?a_i _,
                                 HoRelation : ?R ?o_i2 ?o_j |- _] =>
      specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction) as [reads_s [upds_s [HSemAction_s HdoUpdRegsR]]]
      ; clear HSemAction
    | [HSemAction : SemAction ?o_i1 (?a_i _) _ _ _ _,
                    HERelation : forall _, EffectfulRelation ?R (?a_i _) _,
         HoRelation : ?R ?o_i2 ?o_j |- _] =>
      specialize (HERelation _ _ _ HoRelation _ _ _ _ HSemAction) as [reads_s [upds_s [HSemAction_s HdoUpdRegsR]]]
      ; clear HSemAction
    end.

  Ltac resolve_sublist :=
    let HNoDup := fresh "HNoDup" in
    let HSubList2 := fresh "HSubList" in
    match goal with
    | [Heq : (map (fun x => (fst x, _)) ?o1) = (map (fun y => (fst y, _)) ?o2),
             HSubList1 : SubList ?o1 ?o3 |- _] =>
      assert (NoDup (map fst o3)) as HNoDup
      ;[ reduce_map
         ; decompose_NoDup_string
         ; auto
       | assert (SubList o2 o3) as HSubList2
         ; [prove_sublist
           | specialize (SubList_chain HNoDup HSubList1 HSubList2 (getKindAttr_fst _ _ Heq)) as ?
             ; subst
             ; clear Heq HNoDup HSubList1 HSubList2]
       ]
    | [Heq : (map fst ?o1) = (map fst ?o2),
             HSubList1 : SubList ?o1 ?o3 |- _] =>
      assert (NoDup (map fst o3)) as HNoDup
      ;[ reduce_map
         ; decompose_NoDup_string
         ; auto
       | assert (SubList o2 o3) as HSubList2
         ; [prove_sublist
           | specialize (SubList_chain HNoDup HSubList1 HSubList2 Heq) as ?
             ; subst
             ; clear Heq HNoDup HSubList1 HSubList2]
       ]
    end.

  Lemma SubList_cons_l_iff {B : Type}:
    forall (a : B) (l1 l2 : list B),
      SubList (a :: l1) l2 <->
      In a l2 /\ SubList l1 l2.
  Proof.
    split; intros; rewrite app_cons, SubList_app_l_iff in *; split; try firstorder fail.
    repeat intro; inv H0; dest; auto.
    inv H1.
  Qed.

  Lemma SubList_nil_l {B : Type}:
    forall (l : list B),
      SubList nil l.
  Proof. repeat intro; inv H. Qed.
  
  Ltac mychs' :=
    (match goal with
     | _ => idtac "clean_useless_hyp"; clean_useless_hyp
     | _ => idtac "mySubst"; mySubst
     | _ => idtac "my_simplifier"; my_simplifier 
     | _ => idtac "normalize_key_hyps"; normalize_key_hyps
     | _ => idtac "find_if_inside" ; find_if_inside
     | _ => idtac "simpl_solver"; my_simpl_solver
     | _ => idtac "main"; (match goal with
             | [H: SemAction _ (Return _) _ _ _ _ |- _]
               => apply inversionSemAction' in H; destruct H as [? [? [? ?]]]
             | [H: SemAction _ (MCall _ _ _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H; destruct H as [? [? [? ?]]]
             | [H: SemAction _ (LetAction _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H; destruct H as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]
             | [H: SemAction _ (ReadReg _ _ _) _ _ _ _ |- _]
               => let TMP := fresh "H" in apply inversionSemAction' in H; destruct H as [? [? [TMP [? ?]]]]; decompose_In TMP
             | [H: SemAction _ (WriteReg _ _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H; destruct H as [? [? [? [? ?]]]]
             | [H: SemAction _ (IfElse _ _ _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H;
                  let TMP := fresh "H" in destruct evalExpr eqn:TMP in H; destruct H as [? [? ?]]
             | [H: SemAction _ (LetExpr _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H
             | [H: SemAction _ (ReadNondet _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H; destruct H as [? ?]
             | [H: SemAction _ (Sys _ _) _ _ _ _ |- _]
               => apply inversionSemAction' in H
                           end)
     | _ => idtac "construct";
            (match goal with
             | [ |- SemAction _ (Return _) _ _ _ _ ] => econstructor 10
             | [ |- SemAction _ (MCall _ _ _ _) _ _ _ _] => econstructor 1
             | [ |- SemAction _ (LetAction _ _) _ _ _ _] => econstructor 3
             | [ |- SemAction _ (ReadReg _ _ _) _ _ _ _] => econstructor 5
             | [ |- SemAction _ (WriteReg _ _ _) _ _ _ _] => econstructor 6
             | [ |- SemAction _ (IfElse _ _ _ _) _ _ _ _] => eapply SemAction_if_split
             | [ |- SemAction _ (LetExpr _ _) _ _ _ _] => econstructor 2
             | [ |- SemAction _ (ReadNondet _ _) _ _ _ _] => econstructor 4
             | [ |- SemAction _ (Sys _ _) _ _ _ _] => econstructor 9
             end)
     | _ => idtac "rel_solver";
            (match goal with
             | [ H : SemAction ?o ?a _ _ _ _ |- SemAction ?o ?a _ _ _ _] => apply H
             | [ H : SemAction ?o1 ?a _ _ _ _ |- SemAction ?o2 ?a _ _ _ _] => eapply SemActionExpand;[| apply H]; prove_sublist
             end) 
     (*| [H: match _ with _ => _ end |- _ ] => idtac "match"; progress simpl in H *)
     end).
  
(*   Goal ArbiterCorrect implArbiter specArbiter. *)
(*     destruct implFreeListCorrect. *)
(*     econstructor 1 with (arbiterR := myArbiterR freeListR0 freeListRegs0 outerRegs) (outerRegs := outerRegs). *)
(*     assert (forall (o o' o'' : RegsT) *)
(*                    (HSubList : SubList o (o' ++ o'')) *)
(*                    (HgetKindAttr : getKindAttr o = getKindAttr o') *)
(*                    (HNoDup : NoDup (map fst (o' ++ o''))), *)
(*                o = o') as ReplaceRegsT. *)
(*     { clear. *)
(*       induction o; intros. *)
(*       - destruct o'; auto. *)
(*         inv HgetKindAttr. *)
(*       - induction o'. *)
(*         inv HgetKindAttr. *)
(*         destruct (HSubList _ (in_eq _ _)); subst; inv HgetKindAttr; inv HNoDup. *)
(*         + erewrite IHo; eauto. *)
(*           apply SubList_cons in HSubList; dest. *)
(*           simpl in H1. *)
(*           assert (~In a o). *)
(*           { intro. *)
(*             apply (in_map fst) in H4; apply H2. *)
(*             rewrite map_app, in_app_iff. *)
(*             left; setoid_rewrite <- (getKindAttr_fst _ _ H0); assumption. *)
(*           } *)
(*           eapply SubList_Strengthen; eauto. *)
(*         + exfalso; apply H5. *)
(*           rewrite in_map_iff; exists a; auto. *)
(*     } *)
(*     assert (forall (o o' o'' : RegsT) *)
(*                    (HSubList : SubList o (o'' ++ o')) *)
(*                    (HgetKindAttr : getKindAttr o = getKindAttr o') *)
(*                    (HNoDup : NoDup (map fst (o'' ++ o'))), *)
(*                o = o') as ReplaceRegsT_rev. *)
(*     { clear - ReplaceRegsT. *)
(*       intros; eapply ReplaceRegsT with (o'' := o''); auto. *)
(*       - repeat intro; specialize (HSubList _ H). *)
(*         rewrite in_app_iff in *; firstorder fail. *)
(*       - rewrite map_app, NoDup_app_iff in *; dest; repeat split; auto. *)
(*     } *)
    
(*     assert (forall {B C : Type} (l1 l2 l3 l4 : list (B * C)), *)
(*                DisjKey l3 l4 -> *)
(*                SubList (map fst l1) (map fst l3) -> *)
(*                SubList (map fst l2) (map fst l4) -> *)
(*                DisjKey l1 l2) as DisjKeyShrink. *)
(*     { clear; repeat intro. *)
(*       firstorder fail. *)
(*     } *)
(*     assert (forall {B C : Type} (l1 l2 : list (B * C)), *)
(*                SubList l1 l2 -> *)
(*                SubList (map fst l1) (map fst l2)) as SubListPairs. *)
(*     { clear; repeat intro. *)
(*       rewrite in_map_iff in *; dest. *)
(*       firstorder fail. *)
(*     } *)
(*     all : *)
(*     intros; *)
(*       unfold EffectfulRelation, ActionWb. *)
(*     intros ? ? HArbiterR ? ? ? ? HImpSem. *)
(*     destruct HArbiterR as [ArbiterVal *)
(*                                LocalReg *)
(*                                OuterRegs *)
(*                                LocalRegVal *)
(*                                FreeListImplRegs *)
(*                                FreeListSpecRegs *)
(*                                HImplRegs *)
(*                                HOuterRegs *)
(*                                Ho_iCorrect *)
(*                                Ho_sCorrect *)
(*                                Ho_iNoDup *)
(*                                Ho_sNoDup *)
(*                                HFreeList]. *)
(*       destruct LocalReg; inv LocalRegVal. *)
(*       unfold sendReq, memCallback, arbiterRule, *)
(*       implArbiter, specArbiter, implParams, specParams, *)
(*       arbiterImpl, Impl.sendReq, Impl.nextToAlloc, Impl.alloc, alloc, *)
(*       nextToAlloc, freelist, arbiter in *. *)
(*       repeat mychs'. *)
(*       repeat resolve_wb'. *)
(*       repeat resolve_sublist. *)
(*       repeat resolve_rel'. *)
(*       repeat mychs'. *)
(*       do 2 eexists; split; intros. *)
(*       repeat mychs'; auto. *)
(*       repeat mychs'. *)
(*       repeat mychs'; auto; repeat mychs'; repeat normalize_key_concl; auto. *)

(*       (* Ltac key_sublists := *) *)
(*       (*   match goal with *) *)
(*       (*   | [ |- SubList (map fst ?l1) (map fst ?l2)] *) *)
(*       (*     => *) *)
(*       (*     (match goal with *) *)
(*       (*      | [ H : SubList l1 l2 |- _] => apply (SubList_map fst) in H; assumption *) *)
(*       (*      | [ H : SubList (map (fun x => (fst x, projT1 (snd x))) l1) (map (fun y => (fst y, projT1 (snd y))) l2) *) *)
(*       (*          |- _] => apply (SubList_map fst) in H *) *)
(*       (*                   ; repeat rewrite fst_getKindAttr in H *) *)
(*       (*                   ; assumption *) *)
(*       (*      | [ H : SemAction l1 _ l2 _ _ _ *) *)
(*       (*          |- _] => apply SemActionReadsSub in H *) *)
(*       (*                   ; key_sublists *) *)
(*       (*      | [ H : SemAction l1 _ _ l2 _ _ *) *)
(*       (*          |- _] => apply SemActionUpdSub in H *) *)
(*       (*                   ; key_sublists *) *)
(*       (*      end) *) *)
(*       (*   end. *) *)

(*       Ltac aggressive_key_finder l1 := *)
(*         match goal with *)
(*         | [ H1 : SubList l1 _ |- _] *)
(*           => apply (SubList_map fst) in H1 *)
(*         | [ H1 : SubList (map (fun x => (fst x, projT1 (snd x))) l1) (map (fun y => (fst y, projT1 (snd y))) _) |- _] *)
(*           => apply (SubList_map fst) in H1 *)
(*              ; repeat rewrite fst_getKindAttr in H1 *)
(*         | [ H1 : SemAction _ _ l1 _ _ _ |- _] *)
(*           => apply SemActionReadsSub in H1 *)
(*         | [ H1 : SemAction _ _ _ l1 _ _ |- _] *)
(*           => apply SemActionUpdSub in H1 *)
(*         end. *)
      
(*       Ltac solve_keys := *)
(*         let TMP1 := fresh "H" in *)
(*         let TMP2 := fresh "H" in *)
(*         (match goal with *)
(*          | [ |- ~ In ?a (map fst ?l1)] *)
(*            => idtac "1" *)
(*               ; specialize (SubList_refl (map fst l1)) as TMP1 *)
(*               ; repeat (aggressive_key_finder l1) *)
(*          | [ |- DisjKey ?l1 ?l2] *)
(*            => idtac "2" *)
(*               ; specialize (SubList_refl (map fst l1)) as TMP1 *)
(*               ; specialize (SubList_refl (map fst l2)) as TMP2 *)
(*               ; repeat (aggressive_key_finder l1) *)
(*               ; repeat (aggressive_key_finder l2) *)
(*          end) *)
(*         ; (match goal with *)
(*            | [ H1 : ?P *)
(*                |- ?P] *)
(*              => apply H1 *)
(*            | [ H1 : DisjKey ?l1 ?l2 *)
(*                |- DisjKey ?l2 ?l1] *)
(*              => apply DisjKey_Commutative, H1 *)
(*            | [ H1 : ~ In ?a (map fst ?l2), *)
(*                     H2 : SubList (map fst ?l1) (map fst ?l2) *)
(*                |- ~ In ?a (map fst ?l1)] *)
(*              => idtac "3"; apply (SubList_filter _ H2 H1) *)
(*            | [ H1 : DisjKey ?l1 ?l2, *)
(*                     H2 : SubList (map fst ?l3) (map fst ?l1), *)
(*                          H3 : SubList (map fst ?l4) (map fst ?l2) *)
(*                |- DisjKey ?l3 ?l4] *)
(*              => idtac "4"; apply (DisjKey_filter _ _ H2 H3 H1) *)
(*            | [ H1 : DisjKey ?l1 ?l2, *)
(*                     H2 : SubList (map fst ?l3) (map fst ?l1), *)
(*                          H3 : SubList (map fst ?l4) (map fst ?l2) *)
(*                |- DisjKey ?l4 ?l3] *)
(*              => apply DisjKey_Commutative, (DisjKey_filter _ _ H2 H3 H1) *)
(*            end). *)
(*       solve_keys. *)
(*       solve_keys. *)
(*       repeat mychs'. *)
(*       repeat mychs'. *)
(*       repeat mychs'; auto. *)
(*       repeat mychs'; auto. *)
(*       econstructor. *)
(*       reflexivity. *)
      
(*       Ltac doUpdRegs_simpl_r := *)
(*         match goal with *)
(*         | [ |- context [doUpdRegs _ (_ ++ _)]] => rewrite doUpdRegs_app_r *)
(*         | [ |- context [doUpdRegs _ (_ :: _)]] => rewrite doUpdRegs_cons_r' *)
(*         end. *)

(*       Ltac doUpdRegs_simpl_l := *)
(*         match goal with *)
(*         | [ |- context [doUpdRegs (_ ++ _) _]] => rewrite doUpdRegs_app_l *)
(*         | [ |- context [doUpdRegs (_ :: _) _]] => rewrite doUpdRegs_cons_l' *)
(*         | [ |- context [doUpdReg (_ ++ _) _]] => rewrite doUpdReg_app *)
(*         | [ |- context [doUpdReg (_ :: _) _]] => rewrite doUpdReg_cons *)
(*         end. *)
      
(* (*       *)
(*       Ltac simpl_doupdregs := *)
(*         match goal with *)
(*         | [ |- context [doUpdRegs (_ (_ ++ _))]] => rewrite doUpdRegs_app_r *)
(*         | [ |- context [doUpdRegs (_ ++ _) _]] => rewrite doUpdRegs_app_l *)
(*         | [ |- context [doUpdRegs _ (_ :: nil)]] => cbv beta *)
(*         | [ |- context [doUpdRegs _ (?a :: ?l)]] => rewrite (app_cons a l) *)
(*         | [ |- context [doUpdRegs (_ :: nil) _]] => idtac *)
(*         | [ |- context [doUpdRegs (_ :: _) _]] => rewrite doUpdRegs_cons_l *)
(*         end. *)
(*       Ltac reduce_doupdregs := *)
(*         match goal with *)
(*         | [ HDisjKey : DisjKey ?l1 ?l2 |- context [doUpdRegs ?l1 ?l2]] => rewrite (doUpdRegs_DisjKey l1 l2) *)
(*         | [ Hkey_not_In : key_not_In (fst ?a) ?l1 |- context [doUpdRegs (?a :: nil) ?l1]] => rewrite (doUpdRegs_key_not_In a l1) *)
(*         | [ Hneq : (fst ?a) <> (fst ?b) |- context [doUpdRegs (?a::nil) (?b::nil)]] => rewrite doUpdRegs_keys_neq *)
(*         | [ |- context [map fst (doUpdRegs _ _)]] => rewrite doUpdRegs_preserves_keys *)
(*         | [ HNoDup : NoDup (map fst ?o), *)
(*                      HSubList : SubList (getKindAttr ?u) (getKindAttr ?o) *)
(*             |- context [getKindAttr (doUpdRegs ?u ?o)]] => rewrite (doUpdReg_preserves_getKindAttr HNoDup HSubList) *)
(*         | [ |- context [doUpdRegs nil _] ] => rewrite doUpdRegs_nil *)
(*         end. *)
(* *) *)
(*       3 : { *)
(*         repeat doUpdRegs_simpl_r. *)
(*         repeat doUpdRegs_simpl_l. *)
(*         repeat rewrite doUpdRegs_nil. *)
(*         repeat rewrite doUpdReg_nil. *)
(*         Ltac oneUpdRegs_red := *)
(*           match goal with *)
(*           | [ |- context [ oneUpdRegs ?r ?o]] *)
(*             => let TMP := fresh "H" in *)
(*             assert (~ In (fst r) (map fst o)) as TMP *)
(*             ; [ repeat rewrite doUpdRegs_preserves_keys *)
(*                 ; solve_keys *)
(*               | rewrite (oneUpdRegs_notIn _ _ TMP) *)
(*                 ; clear TMP] *)
(*           end. *)

(*         Ltac doUpdReg_red := *)
(*           match goal with *)
(*           | [ |- context [doUpdReg ?u ?r]] *)
(*             => let TMP := fresh "H" in *)
(*                assert (~ In (fst r) (map fst u)) as TMP *)
(*                ; [ repeat rewrite doUpdRegs_preserves_keys *)
(*                    ; solve_keys *)
(*                  | rewrite (doUpdReg_notIn _ _ TMP) *)
(*                    ; clear TMP] *)
(*           end. *)

(*         Ltac doUpdRegs_red := *)
(*           match goal with *)
(*           | [ |- context [doUpdRegs ?u ?o]] *)
(*             => let TMP := fresh "H" in *)
(*               assert (DisjKey u o) as TMP *)
(*               ; [ repeat rewrite (DisjKey_rewrite_r _ _ _ (doUpdRegs_preserves_keys _ _)) *)
(*                   ; repeat rewrite (DisjKey_rewrite_l _ _ _ (doUpdRegs_preserves_keys _ _)) *)
(*                   ; solve_keys *)
(*                 | rewrite (doUpdRegs_DisjKey TMP) *)
(*                   ; clear TMP] *)
(*           end. *)

(*         Ltac oneUpdReg_red := *)
(*           match goal with *)
(*           | [ |- context [(oneUpdReg (?a, ?b) (?a, ?c))]] *)
(*             => cbv [oneUpdReg]; rewrite String.eqb_refl *)
(*           | [ H : (fst ?r1) = (fst ?r2) |- context [(oneUpdReg ?r1 ?r2)]] *)
(*             => cbv [oneUpdReg]; rewrite String.eqb_sym, <- (String.eqb_eq H) *)
(*           | [ H : (fst ?r2) = (fst ?r1) |- context [(oneUpdReg ?r1 ?r2)]] *)
(*             => cbv [oneUpdReg]; rewrite <- (String.eqb_eq H) *)
(*           | [ H : (fst ?r1) <> (fst ?r2) |- context [(oneUpdReg ?r1 ?r2)]] *)
(*             => cbv [oneUpdReg]; rewrite String.eqb_sym, <- (String.eqb_neq H) *)
(*           | [ H : (fst ?r1) <> (fst ?r2) |- context [(oneUpdReg ?r1 ?r2)]] *)
(*             => cbv [oneUpdReg]; rewrite <- (String.eqb_neq H) *)
(*           end. *)
                       
        
(*         repeat oneUpdRegs_red. *)
(*         repeat doUpdReg_red. *)
(*         repeat doUpdRegs_red. *)
(*         repeat oneUpdReg_red. *)
(*         f_equal. *)
(*       } *)

(*       Ltac aggressive_gka_finder l1 := *)
(*         match goal with *)
(*         | [ H1 : SubList l1 _ |- _] *)
(*           => apply (SubList_map (fun x => (fst x, projT1 (snd x)))) in H1 *)
(*         | [ H1 : SemAction _ _ l1 _ _ _ |- _] *)
(*           => apply SemActionReadsSub in H1 *)
(*         | [ H1 : SemAction _ _ _ l1 _ _ |- _] *)
(*           => apply SemActionUpdSub in H1 *)
(*         end. *)
      
(*       Ltac gka_doUpdReg_red := *)
(*         match goal with *)
(*         | [ |- context [getKindAttr (doUpdRegs ?u ?o)]] *)
(*           => let TMP1 := fresh "H" in *)
(*              let TMP2 := fresh "H" in *)
(*              assert (NoDup (map fst o)) as TMP1 *)
(*              ; [repeat rewrite doUpdRegs_preserves_keys (*a bit weak *) *)
(*                 ; auto *)
(*                | assert (SubList (getKindAttr u) (getKindAttr o)) as TMP2 *)
(*                  ;[ repeat (aggressive_gka_finder u) *)
(*                     ; auto *)
(*                   | rewrite (doUpdReg_preserves_getKindAttr _ _ TMP1 TMP2) *)
(*                     ; clear TMP1 TMP2]] *)
(*         end. *)
                          
        
(*       gka_doUpdReg_red; reflexivity. *)
(*       gka_doUpdReg_red; reflexivity. *)
      
(*       repeat doUpdRegs_simpl_r. *)
(*       repeat doUpdRegs_simpl_l. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       repeat rewrite doUpdReg_nil. *)
      
(*       repeat oneUpdRegs_red. *)
(*       repeat doUpdReg_red. *)
(*       repeat doUpdRegs_red. *)
(*       repeat oneUpdReg_red. *)

(*       f_equal. *)

(*       repeat rewrite doUpdRegs_preserves_keys. *)
(*       repeat mychs'. *)
(*       repeat normalize_key_concl; auto. *)
(*       repeat rewrite doUpdRegs_preserves_keys. *)
(*       repeat mychs'. *)
(*       repeat normalize_key_concl; auto. *)
(*       assumption. *)
      
(*       repeat mychs'. *)
(*       repeat resolve_wb'. *)
(*       repeat resolve_sublist. *)
(*       repeat resolve_rel'. *)
(*       repeat mychs'. *)

(*       do 2 eexists; split; intros. *)

(*       repeat mychs'; auto; repeat mychs'; auto; repeat mychs'. *)
(*       repeat normalize_key_concl; auto. *)
(*       normalize_key_concl; mychs'. *)
(*       mychs'. *)
              
(*       repeat doUpdRegs_simpl_r. *)
(*       repeat doUpdRegs_simpl_l. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       repeat rewrite doUpdReg_nil. *)
      
(*       repeat oneUpdRegs_red. *)
(*       repeat doUpdReg_red. *)
(*       repeat doUpdRegs_red. *)
(*       repeat oneUpdReg_red. *)
(*       econstructor. *)
(*       reflexivity. *)
(*       3 : { *)
(*         f_equal. *)
(*       } *)
(*       3 : { *)
(*         f_equal. *)
(*       } *)
(*       mychs'. *)

(*       gka_doUpdReg_red; mychs'. *)

(*       repeat mychs'. *)
(*       repeat rewrite doUpdRegs_preserves_keys. *)
(*       repeat normalize_key_concl; auto. *)
(*       repeat mychs'. *)
(*       repeat rewrite doUpdRegs_preserves_keys. *)
(*       repeat normalize_key_concl; auto. *)

(*       auto. *)

      
      
(*       repeat mychs'. *)
(*       repeat resolve_wb'. *)
(*       repeat resolve_sublist. *)
(*       repeat resolve_rel'. *)
(*       repeat mychs'. *)
(*       do 2 eexists; split; intros. *)
      
(*       repeat mychs'; auto; repeat mychs'; auto; repeat mychs'. *)

(*       repeat doUpdRegs_simpl_r. *)
(*       repeat doUpdRegs_simpl_l. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       repeat rewrite doUpdReg_nil. *)
      
(*       repeat oneUpdRegs_red. *)
(*       repeat doUpdReg_red. *)
(*       repeat doUpdRegs_red. *)
(*       repeat oneUpdReg_red. *)
(*       econstructor. *)

(*       reflexivity. *)

(*       3 : { *)
(*         f_equal. *)
(*       } *)
(*       reflexivity. *)
(*       reflexivity. *)

(*       repeat mychs'. *)
(*       repeat doUpdRegs_simpl_r. *)
(*       repeat doUpdRegs_simpl_l. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       repeat rewrite doUpdReg_nil. *)

(*       f_equal. *)

(*       repeat mychs'; repeat normalize_key_concl; auto. *)

      
(*       repeat mychs'. *)
(*       repeat doUpdRegs_simpl_r. *)
(*       repeat doUpdRegs_simpl_l. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       repeat rewrite doUpdReg_nil. *)

(*       repeat mychs'; repeat normalize_key_concl; auto. *)

(*       auto. *)

(*       intros. *)
(*       split. *)

(*       unfold sendReq, memCallback, arbiterRule, *)
(*       implArbiter, specArbiter, implParams, specParams, *)
(*       arbiterImpl, Impl.sendReq, Impl.nextToAlloc, Impl.alloc, alloc, *)
(*       nextToAlloc, freelist, arbiter in *. *)
(*       repeat mychs'. *)
(*       exists o; repeat split; auto. *)
(*       apply SubList_refl. *)

(*       Ltac normalize_sublist_l := *)
(*         match goal with *)
(*         | [ |- In _ _] => my_simplifier *)
(*         | [ |- SubList (_ :: _) _] *)
(*           => rewrite SubList_cons_l_iff; split *)
(*         | [ |- SubList (_ ++ _) _] *)
(*           => rewrite SubList_app_l_iff; split *)
(*         end. *)
      
(*       Ltac solve_sublist_l := *)
(*         match goal with *)
(*         | [ |- SubList nil _] *)
(*           => apply (SubList_nil_l _) *)
(*         | [ |- SubList ?l1 _] *)
(*           => repeat (match goal with *)
(*                      | [ H : SemAction _ _ l1 _ _ _ |- _] *)
(*                        => apply SemActionReadsSub in H *)
(*                      end) *)
(*              ; auto *)
(*         end. *)
(*       repeat normalize_sublist_l; repeat solve_sublist_l; auto. *)
(*       5 : { *)
(*         apply SemActionUpdSub in H. *)
(*         apply H. *)
(*       reflexivity. *)
(*       normalize_sublist_l. *)
(*       apply SemActionReadsSub in H1. *)
(*       auto. *)
(*       repeat normalize_sublist_l. *)
(*       rewrite SubListReads in H1. *)
(*       eexists. *)
(*       split. *)
(*       apply SubList_refl. *)
(*       3 : { *)
(*         mychs'. *)
(*         mychs'. *)
(*         2 : { *)
(*           mychs'. *)
(*           2 : { *)
(*             apply H1. *)
(*             } *)
            
(*           3 : { *)
(*             mychs'. *)
(*             mychs'. *)
(*             mychs'. *)
      
(*         assert (DisjKey x6 (doUpdRegs x4 FreeListImplRegs)) as  H. *)
(*         repeat rewrite (DisjKey_rewrite_r _ _ _ (doUpdRegs_preserves_keys _ _)) *)
(*         ; repeat rewrite (DisjKey_rewrite_l _ _ _ (doUpdRegs_preserves_keys _ _)). *)
(*         solve_keys. *)
(*         rewrite (doUpdRegs_DisjKey H). *)
(*         assert (~ In (fst (ArbiterName, existT (fullType type) (SyntaxKind Bool) (evalExpr (Const type true)))) (map fst  (doUpdRegs x6 (doUpdRegs x4 FreeListImplRegs)) )) as  H. *)
(*         repeat rewrite doUpdRegs_preserves_keys. *)
(*         repeat solve_keys. *)
(*         rewrite (oneUpdRegs_notIn _ _ H). *)
(* ; [repeat rewrite doUpdRegs_preserves_keys; solve_keys | rewrite (doUpdReg_notIn _ _  H)]. *)
(*         repeat simpl_doupdregs. *)
(*         repeat reduce_doupdregs. *)
(*         rewrite doUpdRegs_cons_l. *)
(*         repeat rewrite doUpdRegs_app_l. *)
(*         repeat reduce_doupdregs. *)
(*         reduce_doupdregs. *)
(*       simpl. *)
(*       rewrite String.eqb_refl. *)
(*       3 :{ *)
(*         simpl. *)
(*         rewrite String.eqb_refl. *)
(*         f_equal. *)
(*         rewrite app_cons. *)
(*         rewrite doUpdRegs_app_r. *)
(*         reflexivity. *)
(*       } *)
(*       repeat rewrite doUpdRegs_app_foo. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       rewrite doUpdRegs_DisjKey. *)
(*       rewrite doUpdRegs_DisjKey. *)
(*       rewrite doUpdReg_preserves_getKindAttr. *)
(*       reflexivity. *)
(*       admit. (* NoDup map fst deconstruction Ltac? *) *)
(*       assumption. *)
(*       admit. (* DisjKey x (doUpdRegs u o) <-> DisjKey x o *) *)
(*       admit. *)
(*       repeat rewrite doUpdRegs_app_foo. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       rewrite doUpdRegs_DisjKey. *)
(*       rewrite doUpdReg_preserves_getKindAttr. *)
(*       rewrite doUpdRegs_DisjKey. *)
(*       reflexivity. *)
(*       admit. (* SubList (map fst a) (map fst b) -> NoDup (map fst (b ++ c)) -> DisjKey a c ? *) *)
(*       admit. *)
(*       rewrite doUpdRegs_DisjKey. *)
(*       assumption. *)
(*       admit. *)
(*       admit. *)
(*       simpl; rewrite String.eqb_refl; f_equal. *)
(*       rewrite doUpdRegs_app_r. *)
(*       f_equal. *)
(*       rewrite doUpdRegs_cons_foo. *)
(*       rewrite doUpdRegs_DisjKey. *)
(*       rewrite doUpdRegs_cons_foo. *)
(*       rewrite doUpdRegs_app_foo. *)
(*       rewrite doUpdRegs_app_foo. *)
(*       rewrite doUpdRegs_app_foo. *)
(*       admit. *)
(*       admit. *)
(*       rewrite doUpdRegs_preserves_keys; auto. *)
(*       rewrite doUpdRegs_preserves_keys; auto. *)
(*       assert ((doUpdRegs ([(ArbiterName, existT (fullType type) (SyntaxKind Bool) true)] ++ (x6 ++ x2 ++ []) ++ []) FreeListImplRegs) = *)
(*               (doUpdRegs x2 FreeListImplRegs)). *)
(*       { rewrite doUpdRegs_app_foo. *)
(*         rewrite doUpdRegs_app_foo. *)
(*         rewrite doUpdRegs_app_foo. *)
(*         rewrite doUpdRegs_app_foo. *)
(*         repeat rewrite doUpdRegs_nil. *)
(*         rewrite doUpdRegs_DisjKey. *)
(*         rewrite doUpdRegs_DisjKey. *)
(*         reflexivity. *)
(*         admit. *)
(*         admit. } *)
(*         rewrite H0. *)
(*       assert ((doUpdRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) true)::(x6 ++ upds_s ++ []) ++ []) FreeListSpecRegs) = *)
(*               (doUpdRegs upds_s FreeListSpecRegs)). *)
(*       { rewrite doUpdRegs_cons_foo. *)
(*         rewrite doUpdRegs_app_foo. *)
(*         rewrite doUpdRegs_app_foo. *)
(*         rewrite doUpdRegs_app_foo. *)
(*         repeat rewrite doUpdRegs_nil. *)
(*         rewrite doUpdRegs_DisjKey. *)
(*         rewrite doUpdRegs_DisjKey. *)
(*         reflexivity. *)
(*         admit. *)
(*         admit. } *)
(*       rewrite H6. *)
(*       assumption. *)
(*       repeat mychs'. *)
(*       repeat resolve_rel. *)
(*       repeat (simpl in H0; rewrite in_app_iff in H0). *)
(*       foo H0 Ho_iNoDup. *)
(*       do 2 eexists; split; intros. *)
(*       econstructor. *)
(*       simpl; auto. *)
(*       econstructor. *)
(*       all : try reflexivity. *)
(*       2 : { *)
(*         apply HSemAction_s. *)
(*       } *)
(*       apply DisjKey_nil_l. *)
(*       eapply SemAction_if_split. *)
(*       rewrite H4. *)
(*       econstructor. *)
(*       7 : { *)
(*         reflexivity. *)
(*       } *)
(*       2 : { *)
(*         econstructor. *)
(*         simpl; auto. *)
(*         2 : { *)
(*           reflexivity. *)
(*         } *)
(*         2 : { *)
(*           econstructor. *)
(*           econstructor. *)
(*           2 : { *)
(*             apply HSemAction_s0. *)
(*           } *)
(*           2 : { *)
(*             eapply SemAction_if_split; find_if_inside. *)
(*             econstructor. *)
(*             2 : { *)
(*               econstructor; try reflexivity. *)
(*             } *)
(*             apply DisjKey_nil_l. *)
(*             econstructor. *)
(*             all : try reflexivity. *)
(*           } *)
(*           apply DisjKey_nil_r. *)
(*           reflexivity. *)
(*           reflexivity. *)
(*           reflexivity. *)
(*         } *)
(*         assumption. *)
(*       } *)
(*       2 : { *)
(*         econstructor; try reflexivity. *)
(*       } *)
(*       apply DisjKey_nil_r. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       (* Probably not necessary, but a nice addition would be a robust doUpdRegs 'solver' that tried to reduce the size of the upds and cut the o into parts  *)
(*          i.e. doUpdRegs (u1 ++ u2 ++ u3) (o1 ++ o2 ++ o3) = doUpdRegs u1 o1 ++ doUpdRegs u2 o2 ++ doUpdRegs u3 o3. *)
(*        *) *)
(*       assert ((doUpdRegs ([] ++ ((ArbiterName, existT (fullType type) (SyntaxKind Bool) (evalExpr (Const type true))) :: x6 ++ [] ++ []) ++ []) *)
(*                          ((ArbiterName, existT (fullType type) (SyntaxKind Bool) x) :: FreeListImplRegs ++ OuterRegs)) *)
(*                 = *)
(*                 (doUpdRegs ([(ArbiterName, existT (fullType type) (SyntaxKind Bool) (evalExpr (Const type true)))]) ([(ArbiterName, existT (fullType type) (SyntaxKind Bool) x)])) *)
(*                   ++ FreeListImplRegs *)
(*                   ++ (doUpdRegs (x6) (OuterRegs))). *)
(*       { admit. } *)
      
(*       assert ((doUpdRegs ([] ++ ((ArbiterName, existT (fullType type) (SyntaxKind Bool) (evalExpr (Const type true))) :: x6 ++ [] ++ []) ++ []) *)
(*                          ((ArbiterName, existT (fullType type) (SyntaxKind Bool) x) :: FreeListSpecRegs ++ OuterRegs)) *)
(*                 = *)
(*                 (doUpdRegs ([(ArbiterName, existT (fullType type) (SyntaxKind Bool) (evalExpr (Const type true)))]) ([(ArbiterName, existT (fullType type) (SyntaxKind Bool) x)])) *)
(*                   ++ FreeListSpecRegs *)
(*                   ++ (doUpdRegs (x6) (OuterRegs))). *)
(*       { admit. } *)
(*       rewrite H, H0. *)
(*       clear H H0. *)
(*       econstructor. *)
(*       reflexivity. *)
(*       3 : { *)
(*         simpl. *)
(*         rewrite String.eqb_refl. *)
(*         reflexivity. *)
(*       } *)
(*       reflexivity. *)
(*       rewrite doUpdReg_preserves_getKindAttr. *)
(*       reflexivity. *)
(*       admit. *)
(*       assumption. *)
(*       simpl. *)
(*       rewrite String.eqb_refl. *)
(*       reflexivity. *)
(*       rewrite app_cons in Ho_iNoDup. *)
(*       repeat rewrite NoDup_app_DisjKey in *. *)
(*       repeat rewrite DisjKey_app_split_r in *. *)
(*       repeat rewrite DisjKey_app_split_l in *. *)
(*       dest; repeat split; auto. *)
(*       Ltac simplify_keys := *)
(*         match goal with *)
(*         | [ |- context [map fst (doUpdRegs _ _ )] ] => rewrite doUpdRegs_preserves_keys *)
(*         end. *)
(*       simplify_keys; simpl. *)
(*       econstructor; auto. *)
(*       econstructor. *)
(*       simplify_keys; auto. *)
(*       Ltac simplify_DisjKeys := *)
(*         match goal with *)
(*         | [ |- DisjKey (doUpdRegs _ _) _ ] => erewrite DisjKey_same;[|apply doUpdRegs_preserves_keys] *)
(*         | [ |- DisjKey _ (doUpdRegs _ _) ] => apply DisjKey_Commutative; erewrite DisjKey_same; [|apply doUpdRegs_preserves_keys] *)
(*         | [H : DisjKey ?x ?y |- DisjKey ?y ?x ] => apply (DisjKey_Commutative H) *)
(*         end. *)
(*       repeat simplify_DisjKeys. *)
(*       simplify_DisjKeys. *)
(*       assumption. *)
(*       repeat simplify_DisjKeys. *)
(*       rewrite app_cons in Ho_sNoDup. *)
(*       repeat rewrite NoDup_app_DisjKey in *. *)
(*       repeat rewrite DisjKey_app_split_r in *. *)
(*       repeat rewrite DisjKey_app_split_l in *. *)
(*       dest; repeat split; auto. *)
(*       simplify_keys; simpl; auto. *)
(*       simplify_keys; auto. *)
(*       repeat simplify_DisjKeys. *)
(*       repeat simplify_DisjKeys. *)
(*       auto. *)
(*       repeat simplify_DisjKeys. *)
(*       auto. *)
(*       repeat mychs'. *)
(*       repeat resolve_rel. *)
(*       mychs'. *)
(*       repeat (simpl in H0; rewrite in_app_iff in H0). *)
(*       foo H0 Ho_iNoDup. *)
(*       do 2 eexists; split; intros. *)
(*       econstructor. *)
(*       simpl; auto. *)
(*       econstructor. *)
(*       2 : { *)
(*         apply HSemAction_s. *)
(*       } *)
(*       apply DisjKey_nil_l. *)
(*       eapply SemAction_if_split. *)
(*       find_if_inside. *)
(*       econstructor. *)
(*       2 :{ *)
(*         econstructor; reflexivity. *)
(*       } *)
(*       apply DisjKey_nil_l. *)
(*       econstructor; reflexivity. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       find_if_inside. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       reflexivity. *)
(*       repeat rewrite doUpdRegs_nil. *)
(*       econstructor; auto. *)
(*     -  *)
(*       unfold sendReq, memCallback, arbiterRule, *)
(*       implArbiter, specArbiter, implParams, specParams, *)
(*       arbiterImpl, Impl.sendReq, Impl.nextToAlloc, Impl.alloc, alloc, *)
(*       nextToAlloc, freelist, arbiter in *. *)
(*       intros. *)
(*       split. *)
(*       repeat mychs'. *)
(*       repeat resolve_rel. *)
(*       (* *)
                                                         
(*   Ltac resolve_rel := *)
(*     match goal with *)
(*     | [HSemAction1 : SemAction ?o_i ?a_i ?reads ?upds ?calls ?retV, *)
(*        HActionWb : ActionWb ?o1 ?a_i, *)
(*        Ho_iNoDup : NoDup (map fst ?o_i) |- SemAction ?o_s _ _ _ _ _] *)
(*       => match goal with *)
(*          | [HERelation : EffectlessRelation ?R a_i ?a_s, *)
(*             HoRelation : ?R ?o_i1 ?o_j1 |- _] => *)
(*            idtac "hypotheses found R :=" R " o_i1 := " o_i1 " o_j1 := " o_j1; *)
(*            let o_j := fresh "o_j" in *)
(*            let HSL1 := fresh "HSL1" in *)
(*            let HSL2 := fresh "HSL2" in *)
(*            let HCorrect := fresh "HCorrect" in *)
(*            let HSemAction := fresh "HSemAction" in *)
(*            let HR := fresh "HR" in *)
(*            let TMP := fresh "TMP" in *)
(*            let HupdsNil := fresh "HupdsNil" in *)
(*            let HcallsNil := fresh "HcallsNil" in *)
(*            let reads_s := fresh "reads_s" in *)
(*            let HSemAction_s := fresh "HSemAction_s" in *)
(*            specialize (HActionWb _ _ _ _ _ HSemAction1) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR] *)
(*            ;assert (SubList o_i1 o_i) as TMP *)
(*            ;[prove_sublist *)
(*             |rewrite (SubList_chain Ho_iNoDup HSL1 TMP (getKindAttr_fst _ _ HCorrect)) in *; clear TMP] *)
(*            ;specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction_s]]] *)
(*            ; subst *)
(*            ; assert (SubList o_j1 o_s) as TMP *)
(*            ;[prove_sublist *)
(*             | apply (SemActionExpand TMP) in HSemAction_s; clear TMP] *)
(*          | _ => idtac "internal hyp not matched" *)
(*          end *)
(*     | _ => idtac "external hyp not matched"                   *)
(*     end. *)
(* *) *)

      
(*       let Q := fresh H in destruct evalExpr eqn:Q in H3. *)
(*       simpl; auto. *)
(*       simpl in H0; destruct H0 as [Heq | HIn]; [apply inversionPair in Heq as [HName HEqDep]; EqDep_subst; auto *)
(*                                                | simpl in Ho_iNoDup; inversion Ho_iNoDup; apply (in_map fst) in HIn; tauto]. *)
(*       simpl; eauto. *)
(*       3 : { *)
(*         apply inversionSemAction' in H3; dest. *)
(*         destruct evalExpr eqn:G in H3. *)
(*         eapply SemAction_if_split. *)
(*         subst. *)
(*         specialize (nextToAllocWb0 _ _ _ _ _ H2) as [[o_j [HSL1 [HSL2 [HCorrect HSemAction]]]] HR]. *)
(*       assert (SubList FreeListImplRegs *)
(*                       ((ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal) :: FreeListImplRegs ++ OuterRegs)) as P *)
(*       ;[prove_sublist|rewrite (SubList_chain Ho_iNoDup HSL1 P (getKindAttr_fst _ _ HCorrect)) in *; clear P]. *)
(*       specialize (nextToAllocCorrect0 _ _ HFreeList _ _ _ _ HSemAction) as [HupdsNil [HcallsNil [reads_s HSemAction']]]. *)
(*       erewrite G. *)
(*       subst. *)
(*       mychs'; dest. *)
(*       subst. *)
(*       econstructor 3. *)
(*       2 : { *)
(*         eapply (SemActionExpand) with (o := FreeListSpecRegs);[prove_sublist| apply HSemAction']. *)
(*       } *)
(*       apply DisjKey_nil_l. *)
(*       mychs'; dest. *)
(*       simpl in H0. *)
(*       destruct H0 as [Heq | HIn]. *)
(*       apply inversionPair in Heq as [HName HEqDep]. *)
(*       EqDep_subst. *)
(*       mychs'; dest. *)
(*       mychs'; dest. *)
(*       2 : { *)
(*         mychs'; dest. *)
(*         mychs'; dest. *)
(*         simpl; auto. *)
(*         3 : { *)
(*           mychs'; dest. *)
(*           mychs'; dest. *)
(*           apply inversionSemAction' in H7; dest. *)
(*           specialize (H _ _ _ _ _ _ H8) as [[o_j' [HSL1' [HSL2' [HCorrect' HSemAction'']]]] HR']. *)
(*           assert (SubList OuterRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) x) :: FreeListImplRegs ++ OuterRegs)) as P' *)
(*           ; [prove_sublist|rewrite (SubList_chain Ho_iNoDup HSL1' P' (getKindAttr_fst _ _ HCorrect')) in *; clear P']. *)
(*           econstructor 3. *)
(*           2 : { *)
(*             eapply SemActionExpand with (o := OuterRegs); [prove_sublist | apply HSemAction'']. *)
(*           } *)
(*           2 : { *)
(*             mychs'; dest. *)
(*             apply inversionSemAction' in H9; eapply SemAction_if_split. *)
(*             destruct evalExpr eqn:G in H9; rewrite G; dest. *)
(*             mychs'; dest. *)
(*             2 : { *)
(*               mychs'; dest. *)
(*               mychs'; dest. *)
(*               mychs'; dest. *)
(*               mychs'; dest. *)
(*               2 : { *)
(*                 apply inversionSemAction' in H9. *)
(*                 specialize (allocWb0 _ _ _ _ _ _ H9) as [[o_j'' [HSL1'' [HSL2'' [HCorrect'' HSemAction''']]]] HR'']. *)
(*                 assert (SubList FreeListImplRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) x) :: FreeListImplRegs ++ OuterRegs)) as P'' *)
(*                 ; [prove_sublist|rewrite (SubList_chain Ho_iNoDup HSL1'' P'' (getKindAttr_fst _ _ HCorrect'')) in *; clear P'']. *)
(*                 specialize (allocCorrect0 _ _ _ HFreeList _ _ _ _ HSemAction''') as [reads_s' [upds_s' [HSemAction'''' HR''']]]. *)
(*                 econstructor 2. *)
(*                 eapply SemActionExpand with (o := FreeListSpecRegs);[prove_sublist | apply HSemAction'''']. *)
(*                 apply HSemAction'''. *)
(*                 mychs'; dest. *)
                
(*             rewrite G; dest. *)
            
(*             mychs'; dest. *)
(*           specialize (H creqa). *)
        
        
(*         exists o' : list RegT, *)
(*          SubList o' ((ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal) :: FreeListImplRegs ++ OuterRegs) /\ *)
(*          SubList x1 o' /\ getKindAttr o' = getKindAttr OuterRegs /\ SemAction o' ((let (_, _, _, _, nextToAlloc, _, _) := implFreeList in nextToAlloc) type) x1 x2 x3 x7 *)
(*         unfold ActionWb in *. *)
(*         specialize (nextToAllocCorrect0 _ _ HFreeList). *)
(*         eapply nextToAllocCorrect0. *)
(*         eapply SemActionExpand. *)
        
(*         rewrite app_cons. *)
(*         eapply app_sublist_r; reflexivity. *)
(*       simpl in H0. *)
(*       clean_hyp_step. *)
(*       4 : { *)
(*         apply inversionSemAction' in H3. *)
(*         eapply SemAction_if_split. *)
(*         case_eq (evalExpr (! Var type (SyntaxKind Bool) x && ReadStruct (Var type (SyntaxKind (Maybe TransactionTag)) x7) F1)%kami_expr). *)
(*       repeat (mychs'; dest); discharge_SemAction. *)
(*       5 : { *)
(*       (repeat mychs'; dest); discharge_SemAction. *)
      
(*       mychs'; dest. *)
(*       mychs'. *)
(*       mychs'; dest. *)
(*       mychs'. *)
(*       mychs'; dest. *)
      
(*       mychs; discharge_SemAction; eauto. *)
      
      
(*       + unfold Impl.sendReq in *. *)
(*         apply inversionSemAction in HImpSem; dest; subst. *)
(*         unfold arbiter, specParams, implParams in *. *)
(*         econstructor; eauto. *)
(*         * inv H; [left | exfalso]; auto. *)
(*           inv Ho_iNoDup; apply H3; rewrite in_map_iff; exists ((ArbiterName, existT _ _  x)); auto. *)
(*         * apply inversionSemAction in H0; dest; subst. *)
(*           unfold ActionWb in nextToAllocWb0. *)
(*           specialize (nextToAllocWb0 _ _ _ _ _ H1); dest. *)
(*           assert (forall (o o' o'' : RegsT) *)
(*                          (HSubList : SubList o (o' ++ o'')) *)
(*                          (HgetKindAttr : getKindAttr o = getKindAttr o') *)
(*                          (HNoDup : NoDup (map fst (o' ++ o''))), *)
(*                      o = o') as ReplaceRegsT. *)
(*           { clear. *)
(*             induction o; intros. *)
(*             - destruct o'; auto. *)
(*               inv HgetKindAttr. *)
(*             - induction o'. *)
(*               inv HgetKindAttr. *)
(*               destruct (HSubList _ (in_eq _ _)); subst; inv HgetKindAttr; inv HNoDup. *)
(*               + erewrite IHo; eauto. *)
(*                 apply SubList_cons in HSubList; dest. *)
(*                 simpl in H1. *)
(*                 assert (~In a o). *)
(*                 { intro. *)
(*                   apply (in_map fst) in H4; apply H2. *)
(*                   rewrite map_app, in_app_iff. *)
(*                   left; setoid_rewrite <- (getKindAttr_fst _ _ H0); assumption. *)
(*                 } *)
(*                 eapply SubList_Strengthen; eauto. *)
(*               + exfalso; apply H5. *)
(*                 rewrite in_map_iff; exists a; auto. *)
(*           } *)
(*           assert (forall (o o' o'' : RegsT) *)
(*                          (HSubList : SubList o (o'' ++ o')) *)
(*                          (HgetKindAttr : getKindAttr o = getKindAttr o') *)
(*                          (HNoDup : NoDup (map fst (o'' ++ o'))), *)
(*                      o = o') as ReplaceRegsT_rev. *)
(*           { clear - ReplaceRegsT. *)
(*             intros; eapply ReplaceRegsT with (o'' := o''); auto. *)
(*             - repeat intro; specialize (HSubList _ H). *)
(*               rewrite in_app_iff in *; firstorder fail. *)
(*             - rewrite map_app, NoDup_app_iff in *; dest; repeat split; auto. *)
(*           } *)
(*           assert (forall (A : Type) (a : A) (l : list A), *)
(*                      a :: l = [a] ++ l) as app_cons. *)
(*           { auto. } *)
(*           assert (forall o o' k (a : ActionT type k) reads upds calls ret *)
(*                          (HSubList : SubList o o') *)
(*                          (HSemAction : SemAction o a reads upds calls ret), *)
(*                      SemAction o' a reads upds calls ret) as SemActionExpand. *)
(*           { clear. *)
(*             induction a; intros; try (apply inversionSemAction in HSemAction); dest; subst. *)
(*             - econstructor; eauto. *)
(*             - econstructor; eauto. *)
(*             - econstructor; eauto. *)
(*             - econstructor; eauto. *)
(*             - econstructor; eauto. *)
(*             - econstructor; eauto. *)
(*               rewrite in_map_iff in H; dest. *)
(*               specialize (HSubList _ H2). *)
(*               rewrite in_map_iff. *)
(*               exists x0; split; auto. *)
(*             - destruct (evalExpr e) eqn:G; dest;[econstructor 7 | econstructor 8]; eauto. *)
(*             - econstructor; eauto. *)
(*             - econstructor; eauto. *)
(*           } *)
(*           rewrite app_cons in H3, Ho_iNoDup. *)
(*           rewrite (ReplaceRegsT_rev _ _ _ H3 H6 Ho_iNoDup) in *. *)
(*           specialize (nextToAllocCorrect0 _ _ HFreeList _ _ _ _ H7); dest; subst. *)
(*           econstructor. *)
(*           -- apply (DisjKey_nil_l). *)
(*           -- rewrite app_cons. *)
(*              eapply SemActionExpand; eauto. *)
(*              eapply app_sublist_r; eauto. *)
(*           -- apply inversionSemAction in H2; dest. *)
(*              instantiate (1 := if (evalExpr (! Var type (SyntaxKind Bool) x && ReadStruct (Var type (SyntaxKind (Maybe TransactionTag)) x7) F1)%kami_expr) *)
(*                                     then _ else []). *)
(*              destruct evalExpr eqn:G in H8; dest. *)
(*              ++ econstructor 7. *)
(*                 3 : { *)
(*                   apply inversionSemAction in H8; dest. *)
(*                   apply inversionSemAction in H15; dest. *)
(*                   apply inversionSemAction in H15; dest. *)
(*                   apply inversionSemAction in H18; dest. *)
(*                   destruct evalExpr eqn:G0 in H22; dest. *)
(*                   apply inversionSemAction in H22; dest. *)
(*                   apply inversionSemAction in H22; dest. *)
(*                   apply inversionSemAction in H22; dest. *)
(*                   apply inversionSemAction in H22; dest. *)
(*                   specialize (allocWb0 _ _ _ _ _ _ H22); dest. *)
(*                   rewrite app_cons in H28. *)
(*                   rewrite (ReplaceRegsT_rev _ _ _ H28 H31 Ho_iNoDup) in H32. *)
(*                   specialize (allocCorrect0 _ _ _ HFreeList _ _ _ _ H32); dest. *)
(*                   econstructor; simpl; auto. *)
(*                   2 : { *)
(*                     econstructor. *)
(*                     econstructor. *)
(*                     3 : { *)
(*                       econstructor 7. *)
(*                       3 : { *)
(*                         econstructor. *)
(*                         econstructor. *)
(*                         econstructor. *)
(*                         2 : { *)
(*                           econstructor. *)
(*                           eapply SemActionExpand. *)
(*                           rewrite app_cons. *)
(*                           eapply app_sublist_r; reflexivity. *)
(*                           apply H33. *)
(*                         } *)
(*                         apply H27. *)
(*                       } *)
(*                       3 : { *)
(*                         econstructor; auto. *)
(*                       } *)
(*                       apply DisjKey_nil_r. *)
(*                       admit. (* General problem with routerSendReq. *) *)
(*                       reflexivity. *)
(*                       reflexivity. *)
(*                       reflexivity. *)
(*                     } *)
(*                     2 : { *)
(*                       instantiate (4 := nil). *)
(*                       instantiate (3 := nil). *)
(*                       instantiate (2 := x17). *)
(*                       admit. *)
(*                       (* General problem with routerSendReq. *) *)
(*                     } *)
(*                     apply DisjKey_nil_l. *)
(*                     admit. *)
(*                     admit. *)
(*                     admit. *)
(*                   } *)
(*                   2 : { *)
(*                     econstructor. *)
(*                     simpl; auto. *)
(*                     2 : { *)
(*                       simpl; auto. *)
(*                     } *)
(*                     2 : { *)
(*                       econstructor. *)
(*                       econstructor. *)
(*                       3 : { *)
(*                         econstructor 8. *)
(*                         3 : { *)
(*                           econstructor; eauto. *)
(*                         } *)
(*                         apply DisjKey_nil_l. *)
(*                         apply G0. *)
(*                         econstructor. *)
(*                         admit. *)
(*                         all : reflexivity. *)
(*                       } *)
(*                       apply DisjKey_nil_r. *)
(*                       instantiate (3 := nil). *)
(*                       instantiate (2 := nil). *)
(*                       instantiate (1 := x17). *)
(*                       admit. *)
(*                       reflexivity. *)
(*                       reflexivity. *)
(*                       admit. *)
(*                     } *)
(*                     repeat intro; auto. *)
(*                   } *)
(*                   repeat intro; auto. *)
(*                 } *)
(*                 3 : { *)
(*                   apply inversionSemAction in H9; dest. *)
(*                   econstructor; auto. *)
(*                   eauto. *)
(*                 } *)
(*                 apply DisjKey_nil_r. *)
(*                 simpl in H. *)
(*                 destruct H. *)
(*                 apply inversionPair in H; dest. *)
(*                 EqDep_subst. *)
(*                 apply G. *)
(*                 apply (in_map fst) in H. *)
(*                 simpl in Ho_iNoDup; inv Ho_iNoDup. *)
(*                 simpl in H. *)
(*                 contradiction. *)
(*                 reflexivity. *)
(*                 instantiate (1:= (if false *)
(*                                   then [(ArbiterName, existT (fullType type) (SyntaxKind Bool) true)] else [])). *)
(*                 admit. *)
                
(*                 apply inversionSemAction in H8; dest. *)
(*                 apply inversionSemAction in H15; dest. *)
(*                 apply inversionSemAction in H15; dest. *)
(*                 apply inversionSemAction in H18; dest. *)
(*                 destruct evalExpr eqn:G0 in H22; dest. *)
(*                 apply inversionSemAction in H22; dest. *)
(*                 apply inversionSemAction in H22; dest. *)
(*                 apply inversionSemAction in H22; dest. *)
(*                 apply inversionSemAction in H22; dest. *)
(*                 apply inversionSemAction in H9; dest. *)
(*                 apply inversionSemAction in H23; dest. *)
(*                 rewrite H29 in H13. *)
(*                 apply H13. *)
(*                 apply inversionSemAction in H9; dest. *)
(*                 rewrite H28 in H13. *)
(*                 assumption. *)
(*              ++ econstructor 8. *)
(*                 4 : { *)
(*                   apply inversionSemAction in H8; dest. *)
(*                   apply inversionSemAction in H9; dest. *)
(*                   rewrite H8 in H9. *)
(*                   econstructor; auto. *)
(*                   apply H9. *)
(*                 } *)
(*                 apply DisjKey_nil_r. *)
(*                 destruct H. *)
(*                 apply inversionPair in H; dest; EqDep_subst; auto. *)
(*                 apply (in_map fst) in H; simpl in H, Ho_iNoDup; inv Ho_iNoDup. *)
(*                 contradiction. *)
(*                 econstructor. *)
(*                 reflexivity. *)
(*                 reflexivity. *)
(*                 reflexivity. *)
(*                 reflexivity. *)
(*                 simpl; auto. *)
(*                 simpl; auto. *)
(*                 simpl; auto. *)
(*           -- admit. *)
(*           -- auto. *)
(*           -- simpl. *)
(*                 apply inversionSemAction in H22; dest. *)
                  
(*                 ** apply inversionSemAction in H8; apply inversionSemAction in H9; dest. *)
(*                    econstructor; simpl; eauto. *)
(*                    apply inversionSemAction in H18; dest. *)
(*                    econstructor; eauto. *)
(*                    apply inversionSemAction in H18; dest. *)
(*                    econstructor 3 with (readRegs := [(ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal)]) (v := x21); eauto. *)
(*                    admit. (* This has to do with knowing that the routerSendReq has no reads/writes (in the Arbiter module), but it's an empty function right now. *) *)
(*                    apply inversionSemAction in H21; dest. *)
(*                    destruct evalExpr eqn:G0 in H25; dest. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    specialize (allocWb0 _ _ _ _ _ _ H25); dest. *)
(*                    rewrite app_cons in H31. *)
(*                    rewrite (ReplaceRegsT_rev _ _ _ H31 H34 Ho_iNoDup) in H35. *)
(*                    specialize (allocCorrect0 _ _ _ HFreeList _ _ _ _ H35); dest. *)
(*                    econstructor 7. *)
(*                    3 : { *)
(*                      repeat (econstructor; eauto). *)
(*                      eapply SemActionExpand. *)
(*                      rewrite app_cons. *)
(*                      eapply app_sublist_r; reflexivity. *)
(*                      apply H36. *)
(*                    } *)
(*                    3 : { *)
(*                      econstructor; auto. *)
(*                      admit. *)
(*                    } *)
(*                    apply DisjKey_nil_r. *)
(*                    unfold alloc in *. *)
(*                    assumption. *)
(*                    admit. *)
(*                    3 : { *)
(*                      eapply SemActionExpand. *)
(*                      rewrite app_cons. *)
(*                      eapply app_sublist_r; reflexivity. *)
(*                      apply H36. *)
(*                    3 : { *)
(*                      apply inversionSemAction in H26; dest; econstructor; auto. *)
(*                      eauto. *)
(*                    } *)
(*                    6 : { *)
(*                      apply inversionSemAction in H25; dest; econstructor; auto. *)
(*                    } *)
(*                    6 : { *)
(*                      apply inversionSemAction in H26; dest; econstructor; auto. *)
(*                    } *)
(*                    econstructor; auto. *)
(*                    econstructor; auto. *)
(*                    econstructor; auto. *)
(*                    econstructor; auto. *)

(*                    apply DisjKey_nil_r. *)
(*                    eapply SemActionExpand; eauto. *)
(*                    rewrite app_cons. *)
(*                    eapply app_sublist_r; reflexivity. *)
(*                      2 : { *)
(*                        apply H36. *)
(*                      rewrite app_cons. *)
(*                    2 : { *)
(*                      apply inversionSemAction in H26; dest. *)
(*                      econstructor; eauto. *)
(*                    } *)
(*                    2 : { *)
                     
(*                    apply DisjKey_nil_r. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    econstructor; auto. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    econstructor; auto. *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    econstructor. *)
(*                    apply H30. *)
(*                    6 : { *)
(*                      apply inversionSemAction in H25; dest. *)
(*                      apply inversionSemAction in H26; dest. *)
(*                      rewrite H29, H31, H34; reflexivity. *)
(*                    } *)
(*                    5 : { *)
(*                      apply inversionSemAction in H25; dest. *)
(*                      apply inversionSemAction in H26; dest. *)
(*                      rewrite H28, H30, H33; reflexivity. *)
(*                    } *)
(*                    4 : { *)
(*                      apply DisjKey_nil_r. *)
(*                    } *)
(*                    3 : { *)
(*                      apply inversionSemAction in H26; dest. *)
(*                      rewrite H29, H31; reflexivity. *)
(*                    } *)
(*                    apply inversionSemAction in H25; dest. *)
(*                    econstructor; eauto. *)
(*                    apply inversionSemAction in H26; dest. *)
(*                    specialize (allocWb0 _ _ _ _ _ _ H25); dest. *)
(*                    rewrite app_cons in H34. *)
(*                    rewrite (ReplaceRegsT_rev _ _ _ H3 H6 Ho_iNoDup) in *. *)
(*                    specialize (allocCorrect0 _ _ _ HFreeList _ _ _ _ H38). *)
(*                    --- apply inversionSemAction in H25; dest; econstructor; eauto. *)
(*                        apply inversionSemAction in H25; dest; econstructor; eauto. *)
(*                        apply inversionSemAction in H25; dest; econstructor; eauto. *)
(*                        apply inversionSemAction in H25; dest; econstructor; eauto. *)
(*                 ** apply inversionSemAction in H9; dest. *)
(*                    econstructor. *)
(*                    econstructor; eauto. *)
                   
                   
             
(*                (SemActionExpand _ _ _ _ _ _ _ _ (SubList_app_r [(ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal)] (SubList_refl FreeListImplRegs))). *)
              
(*              specialize (SubList_app_r [(ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal)] (SubList_refl FreeListImplRegs)).                           ). *)
              
              
(*           specialize (nextToAllocCorrect0 _ _ HFreeList). *)
(*         inv H; auto. *)
(*         simpl in *; mychs. *)
(*       destruct HArbiterR as [ArbiterVal *)
(*                                LocalReg *)
(*                                FreeListImplRegs *)
(*                                FreeListSpecRegs *)
(*                                HImplRegs *)
(*                                Ho_iCorrect *)
(*                                Ho_sCorrect *)
(*                                Ho_iNoDup *)
(*                                Ho_sNoDup *)
(*                                HFreeList]; *)
(*         try use_correct (nextToAlloc implFreeList type) HFreeList FreeListImplRegs; *)
(*         try use_correct (alloc implFreeList type) HFreeList FreeListImplRegs; *)
(*         try use_correct (free implFreeList type) HFreeList FreeListImplRegs. *)
(*       { *)
(*         repeat mychs; repeat finisher; do 2 eexists; *)
(*           repeat split. *)
(*         { *)
(*           repeat discharge_SemAction; finisher. *)
(*           { *)
(*             match goal with *)
(*             | [H: In ?a (map fst (_ ++ ?b)) |- _] => let H' := fresh in *)
(*                                                    assert (H': In a (map fst ([] ++ b))) by eapply H; clear H'; simpl in H *)
(*             | [H: In ?a (map fst _) |- _] => *)
(*               let H' := fresh in *)
(*               assert (H': In a (map fst [])) by eapply H; clear H'; simpl in H *)
(*             end; intuition. *)
(*           } *)
(*           { *)
(*             subst. *)
(*             match goal with *)
(*             | [H: NoDup ?a |- _] => *)
(*               match a with *)
(*               | context[FreeListImplRegs] => idtac H; inversion H; intuition *)
(*               end *)
(*             end; *)
(*               repeat match goal with *)
(*                      | [H: In _ _ |- _] => eapply inImpInFst in H *)
(*                      | [H: In _ (map fst (getKindAttr FreeListImplRegs)) |- _] => eapply inFstGetKindAttrIffInFst in H; contradiction *)
(*                      end; *)
(*               intuition auto. *)
(*             solve_leftover_Ins FreeListSpecRegs. *)
(*             specialize (nextToAllocCorrect0 _ _ HFreeList). *)
(*             unfold Impl.alloc, alloc in *; simpl in *. *)
(*             (* I think that clean_hyp clobbered the SemAction needed here *) *)
(*             assert ( SemAction ((ArbiterName, existT (fullType type) (SyntaxKind Bool) rv) :: FreeListSpecRegs) ((let (_, _, _, _, nextToAlloc, _, _) := specFreeList in nextToAlloc) type) [] [] [] r1) as RMV_THS. *)
(*             { admit. } *)
(*             apply RMV_THS. *)
(*           } *)
(*           Focus 3. *)
(*           subst. *)
(*           mychs. *)
(*           { admit. } *)
(*           { admit. } *)
(*           all: repeat match goal with *)
(*                       | [|- SemAction _ ?a _ _ _ _] => *)
(*                         lazymatch a with *)
(*                         | context[sendReq] => admit (* we don't know anyting about this yet *) *)
(*                         end *)
(*                       | [|- False] => solve[simpl in *; auto] *)
(*                       end. *)
(*           { *)
(*             subst. *)
(*             right. *)
(*             eapply InGetKindAttr. *)
(*             eapply H.  *)
(*           } *)
(*           { *)
(*             rewrite H0. *)
(*             auto. *)
(*           } *)
(*           { *)
(*             rewrite H0. *)
(*             simpl. *)
(*             f_equal. *)
(*             edestruct AllocCorrect0. (* why is this stuff not being added to the context by the prologue? *) *)
(*             eapply HFreeList. *)
(*             expand_semaction. *)
(*             eapply H9. *)
(*             admit. *)
(*             admit. *)
(*             destruct H6. *)
(*             mychs. (* this needs to happen after the case analysis performed by discharge_SemAction *) *)
(*             reflexivity. *)
(*           } *)
(*         } *)
(*         { *)
(*           discharge_string_dec. *)
(*           simpl findReg.  *)
(*           (* rewrite H. *) *)
(*           discharge_string_dec. *)
(*           repeat rewrite app_nil_r, app_nil_l. *)
(*           simpl in *. *)
(*           discharge_string_dec. *)
(*           rewrite H0. *)
(*           simpl. *)
(*           mychs. *)
(*           econstructor 1 with (ArbiterVal := true) (FreeListImplRegs := *)
(*                                                       doUpdRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) true) :: news0 ++ news2) FreeListImplRegs). *)
(*           { *)

(*             rewrite stripIrrelevantUpd; [> | solve[solve_leftover_Ins FreeListImplRegs]]. *)
(*             symmetry. *)
(*             eapply getKindAttr_doUpdRegs_app; solve[solve_leftover_Ins FreeListImplRegs] || admit. *)
(*           } *)
(*           { *)
(*             trivial. *)
(*           } *)
(*           { *)
(*             discharge_string_dec. *)
(*             reflexivity. *)
(*           } *)
(*           { *)
(*             try rewrite stripIrrelevantUpd; [> | solve[solve_leftover_Ins FreeListImplRegs]]. *)
(*             simpl. *)
(*             constructor. *)
(*             intro. *)
(*             eapply inFstGetKindAttrIffInFst in H2. *)
(*             erewrite <-getKindAttr_doUpdRegs_app in H2. *)
(*             solve_leftover_Ins FreeListImplRegs. *)
(*             solve_leftover_Ins FreeListImplRegs. *)
(*             admit. *)
(*             admit. *)
(*             { *)
(*               eapply NoDupMapFstGetKindAttr. *)
(*               erewrite <-getKindAttr_doUpdRegs_app. *)
(*               eapply NoDupMapFstGetKindAttr. *)
(*               solve_leftover_Ins FreeListImplRegs. solve_leftover_Ins FreeListImplRegs. *)
(*               admit. admit. *)
(*             } *)
(*           } *)
(*           { *)
(*             eapply NoDupMapFstGetKindAttr. *)
(*             erewrite stripIrrelevantUpd. *)
(*             simpl getKindAttr at 1. *)
(*             erewrite <-getKindAttr_doUpdRegs. *)
(*             all: try solve[solve_leftover_Ins FreeListSpecRegs]. *)
(*             solve_leftover_Ins FreeListSpecRegs.  *)
(*             econstructor. *)
(*             intro. eapply H11. *)
(*             admit. *)
(*             finisher. *)
(*             eapply NoDupMapFstGetKindAttr. *)
(*             eauto. *)
(*             admit. *)
(*           } *)
(*           { *)
(*             admit. *)
(*           } *)
(*         } *)
(*         { *)
(*           mychs. *)
(*           repeat discharge_SemAction; finisher; solve_leftover_Ins FreeListImplRegs. *)
(*         } *)
(*         { *)
(*           mychs. *)
(*           econstructor 1 with (ArbiterVal := true) (FreeListImplRegs := *)
(*                                                       doUpdRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) true) :: news0 ++ news2) FreeListImplRegs). *)
(*           { *)
(*             rewrite stripIrrelevantUpd. *)
(*             symmetry. *)
(*             eapply getKindAttr_doUpdRegs_app; solve[solve_leftover_Ins FreeListImplRegs] || admit. *)
(*             solve_leftover_Ins FreeListImplRegs. *)
(*           } *)
(*           { *)
(*             simpl; discharge_string_dec. *)
(*             f_equal. *)
(*             rewrite ?app_nil_r, ?app_nil_l. *)
(*             reflexivity. *)
(*           } *)
(*           { *)
(*             repeat rewrite app_nil_r, app_nil_l. *)
(*             f_equal. *)
(*             simpl in H0. *)
(*             rewrite H0. *)
(*             simpl. *)
(*             discharge_string_dec. *)
(*             auto. *)
(*           } *)
(*           { *)
(*             discharge_string_dec. *)
(*             solve_leftover_Ins FreeListImplRegs. *)
(*           } *)
(*           { *)
(*             repeat rewrite app_nil_r, app_nil_l. *)
(*             simpl. *)
(*             simpl in H0. *)
(*             rewrite H0. *)
(*             simpl. *)
(*             discharge_string_dec. *)
(*             simpl. *)
(*             erewrite stripIrrelevantUpd. *)
(*             econstructor. *)
(*             - *)
(*               intro. *)
(*               eapply inFstGetKindAttrIffInFst in H11. *)
(*               erewrite <-getKindAttr_doUpdRegs in H11. *)
(*               all: solve[solve_leftover_Ins FreeListSpecRegs] || admit. *)
(*             - *)
(*               eapply InGetKindAttr in H1. *)
(*               eapply NoDupMapFstGetKindAttr. *)
(*               erewrite <-getKindAttr_doUpdRegs. *)
(*               eapply NoDupMapFstGetKindAttr. *)
(*               auto. *)
(*               solve_leftover_Ins FreeListSpecRegs. *)
(*               solve_leftover_Ins FreeListSpecRegs. *)
(*               intros. *)
(*               simpl in H10. *)
(*               destruct H10; intuition auto. *)
(*               inversion H10. *)
(*               subst. *)
(*               auto. *)
(*               all: solve[solve_leftover_Ins FreeListSpecRegs] || admit. *)
(*             - *)
(*               solve_leftover_Ins FreeListSpecRegs. *)
(*           } *)
(*           { *)
(*             simpl. *)
(*             simpl in H0. *)
(*             do 2 try rewrite stripIrrelevantUpd; try first [solve [solve_leftover_Ins FreeListSpecRegs] | solve[solve_leftover_Ins FreeListImplRegs]]. *)
(*           } *)
(*         } *)
(*         { *)
(*           mychs. *)
(*           admit. *)
(*         } *)
(*         { *)
(*           repeat rewrite app_nil_r, app_nil_l. *)
(*           simpl. *)

(*           discharge_string_dec. *)
(*           simpl. *)

(*           do 2 try rewrite stripIrrelevantUpd; try first [solve [solve_leftover_Ins FreeListSpecRegs] | solve[solve_leftover_Ins FreeListImplRegs]]. *)
(*           repeat discharge_string_dec. *)
(*           econstructor 1 with (ArbiterVal := true) (FreeListImplRegs := doUpdRegs (news0 ++ news2) FreeListImplRegs) *)
(*                               (FreeListSpecRegs := doUpdRegs *)
(*                                                      [(ArrayName, *)
(*                                                        existT (fullType type) (SyntaxKind (Array len Bool)) *)
(*                                                               (fun i : t len => *)
(*                                                                  if getBool (weq rv1 $(proj1_sig (to_nat i))) *)
(*                                                                  then *)
(*                                                                    if *)
(*                                                                      match Compare_dec.lt_dec # (rv1) len with *)
(*                                                                      | left pf => fun fv : t len -> bool => fv (of_nat_lt pf) *)
(*                                                                      | right _ => fun _ : t len -> bool => false *)
(*                                                                      end rv0 *)
(*                                                                    then *)
(*                                                                      match Compare_dec.lt_dec # (rv1) len with *)
(*                                                                      | left pf => fun fv : t len -> bool => fv (of_nat_lt pf) *)
(*                                                                      | right _ => fun _ : t len -> bool => false *)
(*                                                                      end rv0 *)
(*                                                                    else true *)
(*                                                                  else rv0 i))] FreeListSpecRegs). *)
(*           symmetry. eapply getKindAttr_doUpdRegs_app. *)
(*           solve_leftover_Ins FreeListImplRegs. *)
(*           admit. *)
(*           admit. *)
(*           auto. *)
(*           f_equal. *)
(*           simpl. *)
(*           all: admit. *)
(*         } *)
(*       } *)
(*       { admit. } *)
(*       { admit. } *)
(*     } *)
(*     { admit. } *)
(*     { admit. } *)
(*     { admit. } *)
(*     { admit. } *)
(*     { admit. } *)
(*     Unshelve. *)
(*     all: repeat econstructor. *)
    
(*   Admitted. *)

End Proofs.
