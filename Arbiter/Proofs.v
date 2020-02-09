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
  destruct evalA; eauto; repeat eexists; eauto; destruct (evalExpr p); try discriminate; eexists; split; econstructor; eauto.
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

Variable (B : Type).

(*
clientHandleRes
     : forall (reqK resK : Kind) (a : ArbiterClient reqK resK) (ty : Kind -> Type), ty (clientResK a) -> ActionT ty Void
*)

Record ArbiterCorrect `{ArbiterParams} (imp spec: Arbiter): Type :=
  {
    arbiterRegs: list (Attribute FullKind);
    outerRegs : list (Attribute FullKind);
    arbiterR: RegsT -> RegsT -> Prop;
    sendReqCorrect: forall 
        (req : forall ty : Kind -> Type, ty ArbiterRouterReq -> ActionT ty ArbiterImmRes),
        (forall reqa, ActionWb outerRegs (@req type reqa)) ->
        forall is_err cid creqa , EffectfulRelation arbiterR (@sendReq _ imp is_err req cid type creqa) (@sendReq _ spec is_err req cid type creqa);
    sendReqWb: forall 
        (req : forall ty : Kind -> Type, ty ArbiterRouterReq -> ActionT ty ArbiterImmRes),
        (forall reqa, ActionWb outerRegs (@req type reqa)) ->
        forall is_err cid creqa, ActionWb arbiterRegs (@sendReq _ imp is_err req cid type creqa);
    memCallbackCorrect:
        (forall (reqK resK : Kind) (ac : ArbiterClient reqK resK) cr, ActionWb outerRegs (@clientHandleRes reqK resK ac type cr)) ->
        forall resp, EffectfulRelation arbiterR (@memCallback _ imp type resp) (@memCallback _ spec type resp);
    memCallbackWb: 
      (forall (reqK resK : Kind) (ac : ArbiterClient reqK resK) cr, ActionWb outerRegs (@clientHandleRes reqK resK ac type cr)) ->
      forall resp, ActionWb arbiterRegs (@memCallback _ imp type resp);
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
    | |- SubList ?l1 ?l2 => repeat intro; repeat (simpl in *; rewrite in_app_iff in *); firstorder fail
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
    | [H : ?X = _ |- context[if ?X then _ else _]] => rewrite H
    | [ |- context[if ?X then _ else _]] => let G := fresh "G" in
                                            has_evar X
                                            ; destruct X eqn: G
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

  (* TODO: Replace with more generic, better written, lemmas *)

  Lemma BreakGKAEvar1 {B C : Type} {P : C -> Type} (l1 : list (B * {x : C & P x})) x l2 :
    forall a b l3 p,
      l1 = (a, (existT _ b p)) :: l3 ->
      (a, b) = x ->
      getKindAttr l3 = l2 ->
      getKindAttr l1 = x :: l2.
  Proof. intros; subst; simpl; f_equal. Qed.
  
  Lemma BreakGKAEvar2 {B C : Type} {P : C -> Type} (l1 : list (B * {x : C & P x})) l2 l3 :
    forall l4 l5,
      l1 = l4 ++ l5 ->
      getKindAttr l4 = l2 ->
      getKindAttr l5 = l3 ->
      getKindAttr l1 = l2 ++ l3.
  Proof. intros; subst; rewrite map_app; reflexivity. Qed.
(*
  Lemma gatherActions_ITE ty k_in (acts : list (ActionT ty k_in)) :
    forall k_out cont
        gatherActions
  *)
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
    | [ |- DisjKey (_ ++ _) _] => rewrite DisjKey_app_split_l; split
    | [ |- DisjKey _ (_ ++ _)] => rewrite DisjKey_app_split_r; split
    | [ |- DisjKey (_ :: _) _] => rewrite DisjKey_cons_l_str; split
    | [ |- DisjKey _ (_ :: _)] => rewrite DisjKey_cons_r_str; split
    | [ |- NoDup (_ :: _)] => rewrite NoDup_cons_iff; split
    | [ |- NoDup (_ ++ _)] => rewrite (NoDup_app_Disj_iff string_dec); repeat split                          
    | [ |- key_not_In _ _] => rewrite key_not_In_fst
    | [ |- ~In _ (_ :: _)] => rewrite not_in_cons; split
    | [ |- ~In _ (_ ++ _)] => rewrite (nIn_app_iff string_dec); split
    end.

  Lemma doUpdReg_preserves_keys :
    forall (u : RegsT) (r : RegT),
      fst (doUpdReg u r) = fst r.
  Proof.
    induction u; intros; eauto using doUpdReg_nil.
    unfold doUpdReg; simpl; destruct String.eqb; auto; apply IHu.
  Qed.
  
  Lemma SubList_cons_l_iff {B : Type}:
    forall (a : B) (l1 l2 : list B),
      SubList (a :: l1) l2 <->
      In a l2 /\ SubList l1 l2.
  Proof.
    split; intros; rewrite app_cons, SubList_app_l_iff in *; split; try firstorder fail.
    repeat intro; inv H0; dest; auto.
    inv H1.
  Qed.
  
  Ltac my_simplifier :=
    match goal with
    | [ H1 : ?a = ?b,
            H2 : ?a = ?c |- _] => rewrite H1 in H2
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
    (* | [ |- forall _, (~In _ (map fst ?l1)) \/ (~In _ (map fst ?l2))] => fold (DisjKey l1 l2) *)
    | [ |- context [map _ nil]] => idtac "m_s 4"; rewrite map_nil
    | [ |- context [map _ (_ ++ _)]] => idtac "m_s 5"; rewrite map_app
    | [ |- context [map _ (_ :: _)]] => idtac "m_s 6"; rewrite map_cons
    | [ |- context [In _ (_ :: _)]] => idtac "in_cons_iff concl"; rewrite in_cons_iff
    | [ |- context [In _ (_ ++ _)]] => idtac "in_app_iff concl"; rewrite in_app_iff
    | [ |- context [map fst (doUpdRegs _ _)]] => idtac "doUpdRegs_preserves_keys"; rewrite doUpdRegs_preserves_keys
    | [ |- context [fst (doUpdReg _ _ )]] => idtac "doUpdReg_preserves_keys"; rewrite doUpdReg_preserves_keys
    | [ |- context [doUpdRegs nil _]] => idtac "doUpdRegs_nil"; rewrite doUpdRegs_nil
    | [ |- context [doUpdReg nil _]] => idtac "doUpdReg_nil"; rewrite doUpdReg_nil
    | [ |- ( _ , _ ) = ( _ , _ )] => f_equal
    | [ |- (map (fun x => (fst x, projT1 (snd x))) _) = _ :: _] => eapply BreakGKAEvar1
    | [ |- (map (fun x => (fst x, projT1 (snd x))) _) = _ ++ _] => eapply BreakGKAEvar2
    | [ H : SubList (_ :: _) _ |- _]
      => rewrite SubList_cons_l_iff in H
    | [ H : SubList (_ ++ _) _ |- _]
      => rewrite SubList_app_l_iff in H
    end.

  Lemma SubList_nil_l {B : Type} :
    forall (l : list B),
      SubList nil l.
  Proof. repeat intro; inv H. Qed.
    
  Ltac my_simpl_solver :=
    match goal with
    | [ H : ?P |- ?P] => apply H
    | [ |- DisjKey nil _] => apply DisjKey_nil_l
    | [ |- DisjKey _ nil] => apply DisjKey_nil_r
    | [ |- ?a = ?a] => reflexivity
    | [ |- True] => apply I
    | [ |- NoDup nil] => constructor
    | [ |- ~In _ nil] => intro; my_simpl_solver
(*    | [ |- NoDup (_ :: nil)] => econstructor; my_simpl_solver*)
    | [ H : False |- _] => idtac "False"; exfalso; apply H
    | [ H : ?a <> ?a |- _] => idtac "neq"; exfalso; apply H; reflexivity
    | [ H : In _ nil |- _] => idtac "In nil"; inversion H
    | [ |- SubList nil _ ] => idtac "SubList nil l"; apply SubList_nil_l
    | [ |- ?a = ?b] => (is_evar a; reflexivity || is_evar b; reflexivity)
    end.
  
  Ltac decompose_In H :=
    repeat (rewrite in_cons_iff in H || rewrite in_app_iff in H).
  
  Ltac resolve_wb' :=
      let HNoDup := fresh "H" in
      let HSubList := fresh "H" in
      match goal with
      | [HSemAction1 :SemAction ?o1 ?a_i _ _ _ _,
                      HActionWb : ActionWb ?myR ?a_i |- _] =>
        assert (NoDup (map fst o1)) as HNoDup
        ;[
        | assert (SubList myR (getKindAttr o1)) as HSubList
          ;[clear HNoDup HSemAction1
           | specialize (HActionWb _ _ _ _ _ HNoDup HSubList HSemAction1)
             as [[? [? [? [? ?]]]] ?]
            ; clear HSemAction1 HNoDup HSubList]]
      | [HSemAction1 : SemAction ?o1 (?a_i _) _ _ _ _,
                       HActionWb : forall _, ActionWb ?myR (?a_i _) |- _] =>
        assert (NoDup (map fst o1)) as HNoDup
        ;[
        | assert (SubList myR (getKindAttr o1)) as HSubList
          ;[clear HNoDup HSemAction1
           | specialize (HActionWb _ _ _ _ _ _ HNoDup HSubList HSemAction1)
             as [[? [? [? [? ?]]]] ?]
          ; clear HSemAction1 HNoDup HSubList]]
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
      specialize (HERelation _ _ HoRelation _ _ _ _ HSemAction)
        as [HupdsNil [HcallsNil [reads_s HSemAction_s]]]
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
      ;[ 
      | assert (SubList o2 o3) as HSubList2
        ; [clear HNoDup
        | specialize (SubList_chain HNoDup HSubList1 HSubList2 (getKindAttr_fst _ _ Heq)) as ?
          ; subst
          ; clear Heq HNoDup HSubList1 HSubList2]
      ]
    | [Heq : (map fst ?o1) = (map fst ?o2),
             HSubList1 : SubList ?o1 ?o3 |- _] =>
      assert (NoDup (map fst o3)) as HNoDup
      ;[clear HNoDup
      | assert (SubList o2 o3) as HSubList2
        ; [
         | specialize (SubList_chain HNoDup HSubList1 HSubList2 Heq) as ?
           ; subst
           ; clear Heq HNoDup HSubList1 HSubList2]
      ]
    end.

  Ltac aggressive_key_finder l1 :=
    match goal with
    | [ H1 : SubList l1 _ |- _]
      => apply (SubList_map fst) in H1
    | [ H1 : SubList (map (fun x => (fst x, projT1 (snd x))) l1) (map (fun y => (fst y, projT1 (snd y))) _) |- _]
      => apply (SubList_map fst) in H1
         ; repeat rewrite fst_getKindAttr in H1
    | [ H1 : SemAction _ _ l1 _ _ _ |- _]
      => apply SemActionReadsSub in H1
    | [ H1 : SemAction _ _ _ l1 _ _ |- _]
      => apply SemActionUpdSub in H1
    end.
  
  Ltac solve_keys :=
    let TMP1 := fresh "H" in
    let TMP2 := fresh "H" in
    (match goal with
     | [ |- ~ In ?a (map fst ?l1)]
       => idtac "1"
          ; specialize (SubList_refl (map fst l1)) as TMP1
          ; repeat (aggressive_key_finder l1)
          ; idtac "end 1"
     | [ |- DisjKey ?l1 ?l2]
       => idtac "2"
          ; specialize (SubList_refl (map fst l1)) as TMP1
          ; specialize (SubList_refl (map fst l2)) as TMP2
          ; repeat (aggressive_key_finder l1)
          ; repeat (aggressive_key_finder l2)
          ; idtac "end 2"
     end)
    ; (match goal with
       | [ H1 : ?P
           |- ?P]
         => apply H1
       | [ H1 : DisjKey ?l1 ?l2
           |- DisjKey ?l2 ?l1]
         => apply DisjKey_Commutative, H1
       | [ H1 : ~ In ?a (map fst ?l2),
                H2 : SubList (map fst ?l1) (map fst ?l2)
           |- ~ In ?a (map fst ?l1)]
         => idtac "3"; apply (SubList_filter _ H2 H1)
       | [ H1 : DisjKey ?l1 ?l2,
                H2 : SubList (map fst ?l3) (map fst ?l1),
                     H3 : SubList (map fst ?l4) (map fst ?l2)
           |- DisjKey ?l3 ?l4]
         => idtac "4"; apply (DisjKey_filter _ _ H2 H3 H1)
       | [ H1 : DisjKey ?l1 ?l2,
                H2 : SubList (map fst ?l3) (map fst ?l1),
                     H3 : SubList (map fst ?l4) (map fst ?l2)
           |- DisjKey ?l4 ?l3]
         => apply DisjKey_Commutative, (DisjKey_filter _ _ H2 H3 H1)
       end).
  
  Ltac doUpdRegs_simpl :=
    match goal with
    | [ |- context [doUpdRegs _ (_ ++ _)]] => rewrite doUpdRegs_app_r
    | [ |- context [doUpdRegs _ (_ :: _)]] => rewrite doUpdRegs_cons_r'
    | [ |- context [doUpdRegs (_ ++ _) _]] => rewrite doUpdRegs_app_l
    | [ |- context [doUpdRegs (_ :: _) _]] => rewrite doUpdRegs_cons_l'
    | [ |- context [doUpdReg (_ ++ _) _]] => rewrite doUpdReg_app
    | [ |- context [doUpdReg (_ :: _) _]] => rewrite doUpdReg_cons
    | [H : context [doUpdRegs _ (_ ++ _)] |- _] => rewrite doUpdRegs_app_r in H
    | [H : context [doUpdRegs _ (_ :: _)] |- _] => rewrite doUpdRegs_cons_r' in H
    | [H : context [doUpdRegs (_ ++ _) _] |- _] => rewrite doUpdRegs_app_l in H
    | [H : context [doUpdRegs (_ :: _) _] |- _] => rewrite doUpdRegs_cons_l' in H
    | [H : context [doUpdReg (_ ++ _) _] |- _] => rewrite doUpdReg_app in H
    | [H : context [doUpdReg (_ :: _) _] |- _] => rewrite doUpdReg_cons in H
    end.

  Ltac doUpdRegs_red :=
    match goal with
    | [ |- context [ doUpdRegs nil _]] => idtac "dur_r 1 ("; rewrite doUpdRegs_nil; idtac ")dur_r 1"
    | [ |- context [ doUpdReg nil _]] => idtac "dur_r 2 (";rewrite doUpdReg_nil; idtac ")dur_r 2"
    | [ |- context [ oneUpdRegs ?r ?o]]
      =>idtac "dur_r 3 ("; let TMP := fresh "H" in
         assert (~ In (fst r) (map fst o)) as TMP
         ; [ repeat ( match goal with
                        [ |- context [map fst (doUpdRegs _ _)]]
                        => idtac "doUpdRegs_preserves_keys";
                           rewrite doUpdRegs_preserves_keys
                      end )
             ; solve_keys
           | rewrite (oneUpdRegs_notIn _ _ TMP)
             ; clear TMP]; idtac ")dur_r 3"
    | [ |- context [doUpdReg ?u ?r]]
      =>idtac "dur_r 4("; let TMP := fresh "H" in
         assert (~ In (fst r) (map fst u)) as TMP
         ; [ idtac "dur_r 4_rewr1(" r";; " u ;
             repeat ( match goal with
                        [ |- context [map fst (doUpdRegs _ _)]]
                        => idtac "doUpdRegs_preserves_keys";
                           rewrite doUpdRegs_preserves_keys
                      end );
             idtac ") dur_r 4_rewr1";
             idtac "dur_r 4_solve_keys("; solve_keys; idtac ")dur_r 4_solve_keys"
           | idtac "dur_r 4_rewr2("; rewrite (doUpdReg_notIn _ _ TMP); idtac "dur_r 4_rewr2("
             ; clear TMP]; idtac ")dur_r 4"
    | [ |- context [doUpdRegs ?u ?o]]
      =>idtac "dur_r 5(";
        let TMP := fresh "H" in
        assert (DisjKey u o) as TMP
        ; [ idtac "dur_r 5 rewr1(";
            repeat ( match goal with
                     | [|- DisjKey _ (doUpdRegs _ _)] => rewrite (DisjKey_rewrite_r _ _ _ (doUpdRegs_preserves_keys _ _))
                     | [|- DisjKey (doUpdRegs _ _) _] => rewrite (DisjKey_rewrite_l _ _ _ (doUpdRegs_preserves_keys _ _))
                     end); idtac ")dur_r 5 rewr1"
            ;idtac "dur_r 5_solve_keys("; solve_keys; idtac ")dur_r 5_solve_keys"
          | rewrite (doUpdRegs_DisjKey TMP)
            ; clear TMP]; idtac ")dur_r 5"
    | [ |- context [(oneUpdReg (?a, ?b) (?a, ?c))]]
      => idtac "dur_r 6 ("; cbv [oneUpdReg]; rewrite String.eqb_refl; idtac ")dur_r 6"
    | [ H : (fst ?r1) = (fst ?r2) |- context [(oneUpdReg ?r1 ?r2)]]
      => idtac "dur_r 7("; cbv [oneUpdReg]; rewrite String.eqb_sym, <- (String.eqb_eq H); idtac ")dur_r 7"
    | [ H : (fst ?r2) = (fst ?r1) |- context [(oneUpdReg ?r1 ?r2)]]
      => idtac "dur_r 8("; cbv [oneUpdReg]; rewrite <- (String.eqb_eq H); idtac ")dur_r 8"
    | [ H : (fst ?r1) <> (fst ?r2) |- context [(oneUpdReg ?r1 ?r2)]]
      => idtac "dur_r 9("; cbv [oneUpdReg]; rewrite String.eqb_sym, <- (String.eqb_neq H); idtac ")dur_r 9"
    | [ H : (fst ?r1) <> (fst ?r2) |- context [(oneUpdReg ?r1 ?r2)]]
      => idtac "dur_r 10("; cbv [oneUpdReg]; rewrite <- (String.eqb_neq H); idtac ")dur_r 10"
    end.

  Ltac goal_split :=
    match goal with
    | [ |- ex _] => eexists
    | [ |- _ /\ _] => split
    end.
  
  Ltac aggressive_gka_finder l1 :=
    match goal with
    | [ H1 : SubList l1 _ |- _]
      => apply (SubList_map (fun x => (fst x, projT1 (snd x)))) in H1
    | [ H1 : SemAction _ _ l1 _ _ _ |- _]
      => apply SemActionReadsSub in H1
    | [ H1 : SemAction _ _ _ l1 _ _ |- _]
      => apply SemActionUpdSub in H1
    end.
  
  Ltac gka_doUpdReg_red :=
    match goal with
    | [ |- context [getKindAttr (doUpdRegs ?u ?o)]]
      => let TMP1 := fresh "H" in
         let TMP2 := fresh "H" in
         assert (NoDup (map fst o)) as TMP1
         ; [repeat rewrite doUpdRegs_preserves_keys (*a bit weak *)
            ; auto
           | assert (SubList (getKindAttr u) (getKindAttr o)) as TMP2
             ;[ repeat (aggressive_gka_finder u)
                ; auto
              | rewrite (doUpdReg_preserves_getKindAttr _ _ TMP1 TMP2)
                ; clear TMP1 TMP2]]
    end.


  Ltac normalize_sublist_l :=
    match goal with
    | [ |- In _ _] => my_simplifier
    | [ |- SubList (_ :: _) _]
      => rewrite SubList_cons_l_iff; split
    | [ |- SubList (_ ++ _) _]
      => rewrite SubList_app_l_iff; split
    end.
  
  Ltac solve_sublist_l :=
    match goal with
    | [ |- SubList nil _]
      => apply (SubList_nil_l _)
    | [ |- SubList ?l1 _]
      => repeat (match goal with
                 | [ H : SemAction _ _ l1 _ _ _ |- _]
                   => apply SemActionReadsSub in H
                 end)
         ; auto
    end.
  
  Ltac my_risky_solver :=
    match goal with
    | [ |- _ :: _ = _ :: _ ] => f_equal
    | [ |- _ ++ _ = _ ++ _ ] => f_equal
    | [ H : ?a = ?b |- _] => discriminate
    end.
  
  Ltac aggressive_sublist_finder_l l :=
    match goal with
    | [ H : SemAction _ _ l _ _ _ |- _] => apply SemActionReadsSub in H
    end.
  
  Ltac sublist_sol :=
    let v := fresh "v" in
    let HIn := fresh "H" in
    (match goal with
     | [ |- SubList ?a ?b] =>
       repeat aggressive_sublist_finder_l a
     | [ |- SubList (map (fun x => (fst x, projT1 (snd x))) ?a) (map (fun y => (fst y, projT1 (snd y))) ?b)] =>
       repeat aggressive_gka_finder a
     end)
    ; intros v HIn
    ; repeat my_simplifier
    ; repeat
        (match goal with
         | [HSubList : SubList ?c ?d |- _] =>
           (specialize (HSubList v) || clear HSubList)
         end)
    ; tauto.

  Ltac my_risky_simplifier :=
    match goal with
    | [ |- context [_ ++ nil]] => rewrite app_nil_r
    | [ |- context [nil ++ _]] => rewrite app_nil_l
    end.
  
  Ltac sublist_iff :=
    match goal with
    | [ H : SubList ?l (map (fun x => (fst x, projT1 (snd x))) _)
        |- _] => (match l with
                  | (map (fun y => (fst y, projT1 (snd y))) _) => idtac "sl1" H; revert H; sublist_iff
                  | _ => idtac "sl2" H; rewrite SubList_map_iff in H; dest; sublist_iff
                  end)
    | _ => idtac "fail?"; intros
    end.

  Ltac main_body :=
    match goal with
    | [H: SemAction _ (Return _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
         ; destruct H as [? [? [? ?]]]
    | [H: SemAction _ (MCall _ _ _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
         ; destruct H as [? [? [? ?]]]
    | [H: SemAction _ (LetAction _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
         ; destruct H as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]
    | [H: SemAction _ (ReadReg _ _ _) _ _ _ _ |- _]
      => let TMP := fresh "H" in
         apply inversionSemAction' in H
         ; destruct H as [? [? [TMP [? ?]]]]; decompose_In TMP
    | [H: SemAction _ (WriteReg _ _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
         ; destruct H as [? [? [? [? ?]]]]
    | [H: SemAction _ (IfElse _ _ _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H;
         let TMP := fresh "H" in
         destruct evalExpr eqn:TMP in H
         ; destruct H as [? [? ?]]
    | [H: SemAction _ (LetExpr _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
    | [H: SemAction _ (ReadNondet _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
         ; destruct H as [? ?]
    | [H: SemAction _ (Sys _ _) _ _ _ _ |- _]
      => apply inversionSemAction' in H
    | [H: SemAction _ (gatherActions (map _ ?l) _) _ _ _ _ |- _]
      => idtac " I don't know what to do here, induction will loop"
    end.

  Ltac hyp_consumer :=
    match goal with
     | _ => idtac "sublist_sol["; sublist_sol; idtac "sublist_sol"
     | _ => idtac "normalize_key_concl["; normalize_key_concl; idtac "normalize_key_concl"
     | _ => idtac "clean_useless_hyp["; clean_useless_hyp; idtac "clean_useless_hyp"
     | _ => idtac "mySubst["; mySubst; idtac "mySubst"
     | _ => idtac "my_simplifier["; my_simplifier; idtac "my_simplifier" 
     | _ => idtac "normalize_key_hyps["; normalize_key_hyps; idtac "normalize_key_hyps"
     | _ => idtac "simpl_solver["; my_simpl_solver; idtac "simpl_solver"
     | _ => idtac "find_if_inside["; find_if_inside; idtac "find_if_inside"
     | _ => idtac "resolve_wb'["; resolve_wb'; idtac "resolve_wb'"
     | _ => idtac "resolve_sublist["; resolve_sublist; idtac "resolve_sublist"
     | _ => idtac "resolve_rel'["; resolve_rel'; idtac "resolve_rel'"
(*     | _ => doUpdRegs_simpl; idtac "doUpdRegs_simpl"
     | _ => doUpdRegs_red; idtac "doUpdRegs_red" *)
     | _ => idtac "main["; main_body; idtac "main"
     | _ => idtac "sublist_iff["; sublist_iff; idtac "sublist_iff"
    end.

  Ltac goal_consumer :=
    match goal with
     | _ => goal_split; idtac "goal_split"
     | _ => (match goal with
             | [ |- SemAction _ (Return _) _ _ _ _ ] => econstructor 10
             | [ |- SemAction _ (MCall _ _ _ _) _ _ _ _] => econstructor 1
             | [ |- SemAction _ (LetAction _ _) _ _ _ _] => econstructor 3
             | [ |- SemAction _ (ReadReg _ _ _) _ _ _ _] => econstructor 5
             | [ |- SemAction _ (WriteReg _ _ _) _ _ _ _] => econstructor 6
             | [ |- SemAction _ (IfElse _ _ _ _) _ _ _ _] => eapply SemAction_if_split
             | [ |- SemAction _ (LetExpr _ _) _ _ _ _] => econstructor 2
             | [ |- SemAction _ (ReadNondet _ _) _ _ _ _] => econstructor 4
             | [ |- SemAction _ (Sys _ _) _ _ _ _] => econstructor 9
             end); idtac "construct"
     | _ => (match goal with
             | [ H : SemAction ?o ?a _ _ _ _ |- SemAction ?o ?a _ _ _ _] => apply H
             | [ H : SemAction ?o1 ?a _ _ _ _ |- SemAction ?o2 ?a _ _ _ _] => eapply SemActionExpand;[| apply H]
             end); idtac "rel_solver"
     | _ => solve_keys; idtac "solve_keys"
     | _ => my_risky_simplifier; idtac "risky_simpl"
     | _ => my_risky_solver; idtac "risky_solver"
     | _ => gka_doUpdReg_red; idtac "gka_doUpdReg_red"
     | _ => normalize_sublist_l; idtac "normalize_sublist_l"
    end.
  
  (* Ltac solve_wb := *)
  (*   (match goal with *)
  (*      [ |-  *)
  Ltac mychs' :=
    (match goal with
     | _ => sublist_sol; idtac "sublist_sol"
     | _ => normalize_key_concl; idtac "normalize_key_concl"
     | _ => clean_useless_hyp; idtac "clean_useless_hyp"
     | _ => mySubst; idtac "mySubst"
     | _ => my_simplifier; idtac "my_simplifier" 
     | _ => normalize_key_hyps; idtac "normalize_key_hyps"
     | _ => my_simpl_solver; idtac "simpl_solver"
     | _ => find_if_inside; idtac "find_if_inside"
     | _ => resolve_wb'; idtac "resolve_wb'"
     | _ => resolve_sublist; idtac "resolve_sublist"
     | _ => resolve_rel'; idtac "resolve_rel'"
(*     | _ => doUpdRegs_simpl; idtac "doUpdRegs_simpl"
     | _ => doUpdRegs_red; idtac "doUpdRegs_red" *)
     | _ => main_body; idtac "main"
     | _ => goal_split; idtac "goal_split"
     | _ => sublist_iff; idtac "sublist_iff"
     | _ => (match goal with
             | [ |- SemAction _ (Return _) _ _ _ _ ] => econstructor 10
             | [ |- SemAction _ (MCall _ _ _ _) _ _ _ _] => econstructor 1
             | [ |- SemAction _ (LetAction _ _) _ _ _ _] => econstructor 3
             | [ |- SemAction _ (ReadReg _ _ _) _ _ _ _] => econstructor 5
             | [ |- SemAction _ (WriteReg _ _ _) _ _ _ _] => econstructor 6
             | [ |- SemAction _ (IfElse _ _ _ _) _ _ _ _] => eapply SemAction_if_split
             | [ |- SemAction _ (LetExpr _ _) _ _ _ _] => econstructor 2
             | [ |- SemAction _ (ReadNondet _ _) _ _ _ _] => econstructor 4
             | [ |- SemAction _ (Sys _ _) _ _ _ _] => econstructor 9
             end); idtac "construct"
     | _ => (match goal with
             | [ H : SemAction ?o ?a _ _ _ _ |- SemAction ?o ?a _ _ _ _] => apply H
             | [ H : SemAction ?o1 ?a _ _ _ _ |- SemAction ?o2 ?a _ _ _ _] => eapply SemActionExpand;[| apply H]
             end); idtac "rel_solver"
     | _ => solve_keys; idtac "solve_keys"
     | _ => my_risky_simplifier; idtac "risky_simpl"
     | _ => my_risky_solver; idtac "risky_solver"
     | _ => gka_doUpdReg_red; idtac "gka_doUpdReg_red"
     | _ => normalize_sublist_l; idtac "normalize_sublist_l"
(*     | [H: match _ with _ => _ end |- _ ] => idtac "match"; progress simpl in H *)
     end).

  Ltac doUpdRegs_solv :=
    match goal with
    | _ => doUpdRegs_simpl; idtac "doUpdRegs_simpl"
    | _ => doUpdRegs_red; idtac "doUpdRegs_red"
    end.

  Ltac Record_construct :=
    match goal with
    | [ |- myArbiterR _ _ _ _ _ ] => econstructor
    end.

  Ltac Record_destruct :=
    match goal with
    | [ H : myArbiterR _ _ _ _ _ |- _] => destruct H
    end.
  
  Ltac simple_tactic :=
    repeat mychs'; doUpdRegs_solv.
        Ltac resolve_wb'' :=
        let HNoDup := fresh "H" in
        let HSubList := fresh "H" in
        match goal with
        | [HSemAction1 :SemAction ?o1 ?a_i _ _ _ _,
                        HActionWb : ActionWb ?myR ?a_i |- _] =>
          idtac "1";
          assert (NoDup (map fst o1)) as HNoDup
          ;[
          | assert (SubList myR (getKindAttr o1)) as HSubList
            ;[clear HNoDup HSemAction1
             | specialize (HActionWb _ _ _ _ _ HNoDup HSubList HSemAction1)
               as [[? [? [? [? ?]]]] ?]
               ; clear HSemAction1 HNoDup HSubList]]
        | [HSemAction1 : SemAction ?o1 (?a_i _) _ _ _ _,
                         HActionWb : forall _, ActionWb ?myR (?a_i _) |- _] =>
          idtac "2"
        | [HSemAction1 : SemAction ?o1 (?a_i _ _) _ _ _ _,
                         HActionWb : forall _ _, ActionWb ?myR (?a_i _ _) |- _] =>
          idtac "3"
        | [HSemAction1 : SemAction ?o1 (?a_i _ _ _) _ _ _ _,
                         HActionWb : forall _ _ _, ActionWb ?myR (?a_i _ _ _) |- _] =>
          idtac "4"
        | [HSemAction1 : SemAction ?o1 (?a_i _ _ _ _ _) _ _ _ _,
                         HActionWb :  forall _ _ _ _, ActionWb ?myR (?a_i _ _ _ _ _)|- _] =>
          idtac "5" HActionWb myR a_i;
          assert (NoDup (map fst o1)) as HNoDup
          ;[
          | assert (SubList myR (getKindAttr o1)) as HSubList
            ;[clear HNoDup HSemAction1
             | specialize (HActionWb _ _ _ _ _ _ _ _ _ HNoDup HSubList HSemAction1)
               as [[? [? [? [? ?]]]] ?]
               ; clear HSemAction1 HNoDup HSubList]]
        | [HSemAction1 : SemAction ?o1 (?a_i _ _ _ _ _) _ _ _ _,
                         HActionWb : forall _ _ _ _ _, ActionWb ?myR (?a_i _ _ _ _ _) |- _] =>
          idtac "6"
        end.
  
  Goal ArbiterCorrect implArbiter specArbiter.
    assert (forall {B: Type} {k_in k_out} (f : B -> ActionT type k_in) myReg
                   (cont : ActionT type k_out),
               ActionWb myReg cont ->
               (forall (b : B),
                   ActionWb myReg (f b)) ->
               forall (l : list B),
                 ActionWb myReg (gatherActions (map f l) (fun val => cont))) as gatherAction_invar.
    { clear.
      induction l; simpl; intros; auto.
      unfold ActionWb; intros.
      repeat main_body; subst.
      specialize (H0 _ _ _ _ _ _ H1 H2 H4); dest.
      specialize (IHl _ _ _ _ _ H1 H2 H5); dest.
      eexists; repeat goal_split.
      apply H10.
      rewrite SubList_app_l_iff; split; auto.
      subst; repeat hyp_consumer.
      auto.
      clear H4 H5.
      repeat hyp_consumer.
      repeat goal_consumer.
      assumption.
      repeat hyp_consumer.
      repeat goal_consumer.
      auto.
      auto.
    }
    assert (forall k (a : ActionT type k) myRegs1 myRegs2,
               SubList myRegs1 myRegs2 ->
               ActionWb myRegs1 a ->
               ActionWb myRegs2 a) as ActionWbExpand.
    { clear.
      unfold ActionWb; intros.
      specialize (H0 _ _ _ _ _ H1 (SubList_transitive H H2) H3); dest.
      rewrite SubList_map_iff in H2; dest.
      assert (SubList x x0).
      { rewrite <- H8, <- H6 in H.
        repeat intro.
        specialize (H0 _ H9).
        specialize (in_map fst _ _ H9) as P.
        apply (SubList_map fst) in H; repeat rewrite fst_getKindAttr in H.
        specialize (H _ P).
        rewrite in_map_iff in H; dest.
        specialize (H2 _ H10).
        rewrite (KeyMatching3 _ _ _ H1 H0 H2 (eq_sym H)).
        assumption.
      }
      split.
      - exists x0; repeat split; auto.
        + apply (SubList_transitive H5 H9).
        + eapply SemActionExpand; [apply H9| assumption].
      - apply (SubList_transitive H4 H).
    }
    assert (ActionWb nil Retv%kami_action) as RetvWb.
    { clear.
      unfold ActionWb; intros.
      repeat hyp_consumer.
      repeat goal_split.
      - instantiate (1 := nil).
        apply SubList_nil_l.
      - apply SubList_nil_l.
      - auto.
      - constructor; auto.
      - apply SubList_nil_l.
    }
    destruct implFreeListCorrect.
    econstructor 1 with (arbiterR:= myArbiterR freeListR0 freeListRegs0 outerRegs)
                        (outerRegs := outerRegs)
                        (arbiterRegs := (ArbiterName, SyntaxKind Bool) :: freeListRegs0 ++ outerRegs).
    all :
    intros;
      unfold EffectfulRelation, ActionWb; intros
      ; try Record_destruct; try (destruct LocalReg; inv LocalRegVal);
        unfold sendReq, memCallback, arbiterRule,
        implArbiter, specArbiter, implParams, specParams,
        arbiterImpl, Impl.sendReq, Impl.nextToAlloc,
        Impl.alloc, Impl.memCallback, Impl.arbiterRule,
        Impl.free, alloc, free,
        nextToAlloc, freelist, arbiter in *.
    1 :{
      repeat (repeat hyp_consumer; repeat goal_consumer).
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      auto.
      auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      repeat doUpdRegs_simpl; repeat doUpdRegs_red; Record_construct.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      auto.
      auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      repeat doUpdRegs_simpl; repeat doUpdRegs_red; Record_construct.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      auto.
      auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      repeat doUpdRegs_simpl; repeat doUpdRegs_red; Record_construct.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
    }
    4 : {
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      repeat doUpdRegs_simpl; repeat doUpdRegs_red; Record_construct.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
    }
    1 : {
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      6 : auto.
      6 : auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      2 : auto.
      2 : auto.
      2 : auto.
      2 : auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      4 : auto.
      8 : auto.
      6 : auto.
      6 : auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      auto.
      auto.
      4 : auto.
      5 : auto.
      3 : auto.
      all : repeat (repeat hyp_consumer; repeat goal_consumer).
      3 : auto.
      2 : auto.
      auto.
    }
    3 : {
      repeat (repeat hyp_consumer).
      rewrite in_map_iff in H1; dest.
      repeat (repeat hyp_consumer).
      destruct x2, s0; simpl in *; subst.
      repeat (repeat hyp_consumer; repeat goal_consumer).
      2 : auto.
      2 : auto.
      2 : auto.
      2 : auto.
      repeat (repeat hyp_consumer; repeat goal_consumer).
      apply H4.
      auto.
    }
    1 : { 
      repeat (repeat hyp_consumer).
      Ltac extract_gatherActions subRegs :=
        match goal with
        | [ H : SemAction ?o (gatherActions (map ?f ?l) (fun _ : _ => ?s)) _ _ _ _ |- _]
          => idtac "f" f "l" l "s" s;
             assert (ActionWb (getKindAttr subRegs) s /\
                     (forall t,
                         ActionWb (getKindAttr subRegs) (f t)) /\
                     SubList subRegs o)
        end.
      extract_gatherActions OuterRegs.
      { repeat goal_consumer; intros.
        eapply ActionWbExpand.
        2 : {
          unfold ActionWb; intros.
          repeat main_body.
          repeat mySubst.
          repeat goal_consumer.
          5 : auto.
          5 : auto.
          5 : auto.
          4 : auto.
          3 : auto.
          2 : my_simpl_solver.
          2 : my_simplifier; my_simpl_solver.
          instantiate (1 := nil).
          my_simpl_solver.
        }
        repeat my_simplifier; repeat my_simpl_solver.
        eapply ActionWbExpand.
          2 : {
            unfold ActionWb; intros.
            repeat main_body.
            repeat mySubst.
            repeat clean_useless_hyp.
            resolve_wb''.
            repeat my_simpl_solver.
            2 : {
              repeat goal_consumer.
              4 : {
                find_if_inside.
                goal_consumer.
                all : repeat my_simpl_solver.
                3 : repeat goal_consumer.
                all : repeat my_simpl_solver.
                all : repeat my_simpl_solver.
                goal_consumer.
                goal_consumer.
                apply H22.
              }
              my_simpl_solver.
              my_simpl_solver.
              all : repeat find_if_inside.
              all : repeat my_risky_simplifier; repeat my_simpl_solver.
              eapply H21.
              auto.
            }
            my_simpl_solver.
            repeat mySubst.
            repeat clean_useless_hyp.
            rewrite SubList_map_iff in H13; dest.
            repeat goal_consumer.
            4 : {
              find_if_inside.
              repeat goal_consumer.
              all : repeat my_simpl_solver.
              my_simpl_solver.
            }
            all : try find_if_inside.
            all : repeat my_simplifier; repeat my_simpl_solver.
            all : repeat my_risky_simplifier; repeat my_simpl_solver.
            apply H13.
            apply H14.
          }
          apply SubList_refl.
          sublist_sol.
        }
      dest.
      specialize (gatherAction_invar _ _ _ _ _ _ H11 H13 (getFins numClients)).
      resolve_wb'.
      repeat hyp_consumer.
      eapply SubList_map.
      repeat hyp_consumer.
      repeat (repeat hyp_consumer; repeat goal_consumer).
      repeat doUpdRegs_simpl; repeat doUpdRegs_red; Record_construct.
      repeat (repeat hyp_consumer; repeat goal_consumer).
      3 : auto.
      3 : auto.
      all : try gka_doUpdReg_red; try my_simpl_solver.
      repeat (repeat hyp_consumer; repeat goal_consumer).
      repeat (repeat hyp_consumer; repeat goal_consumer).
    }
    1 : { 
      repeat (repeat hyp_consumer).
      Ltac extract_gatherActions' :=
        match goal with
        | [ H : SemAction ?o (gatherActions (map ?f ?l) (fun _ : _ => ?s)) _ _ _ _ |- _]
          => assert (exists subRegs,
                        (ActionWb (getKindAttr subRegs) s /\
                         (forall t',
                             ActionWb (getKindAttr subRegs) (f t')) /\
                         SubList subRegs o))
        end.
      extract_gatherActions'.
      { repeat goal_consumer; intros.
        eapply ActionWbExpand.
        2 :{
          unfold ActionWb; intros.
          repeat hyp_consumer.
          repeat goal_consumer.
          all : try my_simpl_solver.
          2 : auto.
          instantiate (1 := nil); repeat hyp_consumer.
        }
        repeat hyp_consumer.
        eapply ActionWbExpand.
        2 :{
          unfold ActionWb; intros.
          repeat hyp_consumer.
          resolve_wb''.
          hyp_consumer.
          apply H7.
          repeat goal_consumer.
          all : repeat find_if_inside.
          5 : auto.
          5 : auto.
          5 : auto.
          5 : auto.
          all : try my_simpl_solver.
          4 : repeat goal_consumer.
          all : try my_simpl_solver.
          all : repeat my_risky_simplifier; repeat my_simpl_solver.
          5 : auto.
          apply H.
          assumption.
          assumption.
          apply SubList_refl.
          rewrite SubList_map_iff in H7; dest.
          repeat goal_consumer.
          all : try my_simpl_solver.
          3 : {
            find_if_inside.
            repeat goal_consumer.
            all : try my_simpl_solver.
            my_simpl_solver.
          }
          all : try find_if_inside.
          all : repeat my_risky_simplifier; repeat my_simpl_solver.
          apply H7.
          assumption.
        }
        apply H4.
        apply SubList_refl.
      }
      dest.
      specialize (gatherAction_invar _ _ _ _ _ _ H5 H7 (getFins numClients)).
      resolve_wb'.
      repeat hyp_consumer.
      eapply SubList_map.
      repeat hyp_consumer.
      rewrite in_map_iff in H1; dest.
      rewrite SubList_map_iff in H4; dest.
      destruct x10, s0 in *.
      simpl in *.
      repeat my_simplifier.
      repeat goal_consumer.
      5 : auto.
      4 : {
        rewrite <- H1, H14.
        repeat hyp_consumer.
        reflexivity.
        reflexivity.
      }
      repeat normalize_sublist_l.
      apply H6.
      assumption.
      assumption.
      sublist_sol.
      2 : sublist_sol.
      3 : sublist_sol.
      resolve_sublist.
      auto.
      auto.
      admit.
      admit.
      admit.
      Unshelve.
      all : repeat econstructor.
      all : auto.
      admit.
      admit.
    }
    Admitted.

End Proofs.
