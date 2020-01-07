Require Import Kami.All.
Require Import StdLibKami.Arbiter.Impl.
Require Import StdLibKami.FreeList.Spec.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.Arbiter.AuxLemmas.
Require Import StdLibKami.Arbiter.AuxLtac.
Require Import StdLibKami.FreeList.Ifc.
Require Import Coq.Logic.EqdepFacts.
Require Import StdLibKami.KamiCorrectness.

(*
Record FreeListCorrect {len} (imp spec: @FreeList len): Type :=
  {
    FreeListRegs: list (Attribute FullKind);
    FreeListR: RegsT -> RegsT -> Prop;
    NextToAllocCorrect: EffectlessRelation FreeListR (imp.(nextToAlloc)) (spec.(nextToAlloc));
    NextToAllocWb: ActionWb FreeListRegs FreeListR (imp.(nextToAlloc));
    AllocCorrect: forall allocand, EffectfulRelation FreeListR (imp.(alloc) allocand) (spec.(alloc) allocand);
    AllocWb: forall allocand, ActionWb FreeListRegs FreeListR (imp.(alloc) allocand);
    FreeCorrect: forall input, EffectfulRelation FreeListR (imp.(free) input) (spec.(free) input);
    FreeWb: forall input, ActionWb FreeListRegs FreeListR (imp.(free) input);
  }.

Record ArbiterCorrect `{ArbiterParams} {k} (imp spec: @Arbiter k): Type :=
  {
    ArbiterRegs: list (string * FullKind);
    ArbiterR: RegsT -> RegsT -> Prop;
    clientReqGenCorrect: forall id req, EffectfulRelation ArbiterR (imp.(sendReq) id type req) (spec.(sendReq) id type req);
    clientReqGenWb: forall id req, ActionWb ArbiterRegs ArbiterR (imp.(clientReqGen) id type req);
    memCallbackCorrect: forall resp, EffectfulRelation ArbiterR (imp.(memCallback) type resp) (spec.(memCallback) type resp);
    memCallbackWb: forall resp, ActionWb ArbiterRegs ArbiterR (imp.(memCallback) type resp);
    ruleCorrect: EffectfulRelation ArbiterR (imp.(arbiterRule) type) (spec.(arbiterRule) type);
    ruleWb: ActionWb ArbiterRegs ArbiterR (imp.(arbiterRule) type);
  }.

Section Proofs.
  (** * Common parameters *)
  Context `{A: ArbiterParams}.
  Context (memReq: forall ty, ty MemReq -> ActionT ty Bool).
  
  (** * Spec parameters *)
  Context (ArrayName: string).
  Definition specFreeListParams: FreeListParams := Build_FreeListParams serverTagSz ArrayName.
  Context (ArbiterName: string).
  Context (AlistRead AlistWrite: string).
  Definition specFreeList := (@specFreeList specFreeListParams).
  Definition specParams: ArbiterImplParams :=
    Build_ArbiterImplParams ArbiterName
                            AlistRead
                            AlistWrite
                            specFreeList
                            memReq.
  
  (** * Impl parameters *)
  Context (implFreeList: @FreeList serverTagNum).
  Context (implFreeListCorrect: FreeListCorrect implFreeList specFreeList).
  Definition implParams: ArbiterImplParams :=
    Build_ArbiterImplParams ArbiterName
                            AlistRead
                            AlistWrite
                            implFreeList
                            memReq.
  
  (** * The arbiter pseudo-modules involved in the correctness proof *)
  Definition specArbiter := @arbiterImpl A specParams.
  Definition implArbiter := @arbiterImpl A implParams.
  

  Record myArbiterR (freelistR: RegsT -> RegsT -> Prop) freelistRegs (o_i o_s: RegsT): Prop :=
    {
      ArbiterVal: bool;
      LocalReg: RegT := (ArbiterName, existT (fullType type) (SyntaxKind Bool) ArbiterVal);
      FreeListImplRegs: RegsT;
      FreeListSpecRegs: RegsT;
      HImplRegs: (getKindAttr FreeListImplRegs) = freelistRegs;
      Ho_iCorrect: o_i = LocalReg :: FreeListImplRegs;
      Ho_sCorrect: o_s = LocalReg :: FreeListSpecRegs;
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
                          | [H: SemAction _ (Impl.alloc type _) _ _ _ _ |- _] => revert H
                          | [H: SemAction _ (alloc implFreeList type _) _ _ _ _ |- _] => revert H
                          | [H: SemAction _ (Impl.nextToAlloc type) _ _ _ _ |- _] => revert H
                          | [H: SemAction _ (nextToAlloc implFreeList type) _ _ _ _ |- _] => revert H
                          | [H: SemAction _ (Impl.free type _) _ _ _ _ |- _] => revert H
                          | [H: SemAction _ (memReq type _) _ _ _ _ |- _] => revert H
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

  Goal ArbiterCorrect implArbiter specArbiter.
    destruct implFreeListCorrect.
    econstructor 1 with (ArbiterR := myArbiterR FreeListR0 FreeListRegs0).
    all:
      intros;
      unfold EffectfulRelation.
    {
      intros ? ? HArbiterR ? ? ? ? HImpSem;
        simpl in *;
        mychs; (* can be thought of as clean_hyp_step: here it simply
                  extracts as much info from the
                  [ SemAction _ (clientReqGen implArbiter id type req) ... ]
                  hypothesis as possible as in the ordinary clean_hyp_step tactic *)
        destruct HArbiterR as [ArbiterVal
                                 LocalReg
                                 FreeListImplRegs
                                 FreeListSpecRegs
                                 HImplRegs
                                 Ho_iCorrect
                                 Ho_sCorrect
                                 Ho_iNoDup
                                 Ho_sNoDup
                                 HFreeList];
        simpl in HImplRegs;
        try use_correct (nextToAlloc implFreeList type) HFreeList FreeListImplRegs;
        try use_correct (alloc implFreeList type) HFreeList FreeListImplRegs;
        try use_correct (free implFreeList type) HFreeList FreeListImplRegs.
      {
        repeat mychs; repeat finisher; do 2 eexists;
          repeat split.
        {
          repeat discharge_SemAction; finisher.
          {
            match goal with
            | [H: In ?a (map fst (_ ++ ?b)) |- _] => let H' := fresh in
                                                   assert (H': In a (map fst ([] ++ b))) by eapply H; clear H'; simpl in H
            | [H: In ?a (map fst _) |- _] =>
              let H' := fresh in
              assert (H': In a (map fst [])) by eapply H; clear H'; simpl in H
            end; intuition.
          }
          {
            subst.
            match goal with
            | [H: NoDup ?a |- _] =>
              match a with
              | context[FreeListImplRegs] => idtac H; inversion H; intuition
              end
            end;
              repeat match goal with
                     | [H: In _ _ |- _] => eapply inImpInFst in H
                     | [H: In _ (map fst (getKindAttr FreeListImplRegs)) |- _] => eapply inFstGetKindAttrIffInFst in H; contradiction
                     end;
              intuition auto.
            solve_leftover_Ins FreeListSpecRegs.
            admit.
          }
          { admit. }
          all: repeat match goal with
                      | [|- SemAction _ ?a _ _ _ _] =>
                        lazymatch a with
                        | context[memReq] => admit (* we don't know anyting about this yet *)
                        end
                      | [|- False] => solve[simpl in *; auto]
                      end.
          {
            subst.
            right.
            eapply InGetKindAttr.
            eapply H. 
          }
          {
            rewrite H0.
            auto.
          }
          {
            rewrite H0.
            simpl.
            f_equal.
            edestruct AllocCorrect0. (* why is this stuff not being added to the context by the prologue? *)
            eapply HFreeList.
            expand_semaction.
            eapply H9.
            admit.
            admit.
            destruct H6.
            mychs. (* this needs to happen after the case analysis performed by discharge_SemAction *)
            reflexivity.
          }
        }
        {
          discharge_string_dec.
          simpl findReg. 
          (* rewrite H. *)
          discharge_string_dec.
          repeat rewrite app_nil_r, app_nil_l.
          simpl in *.
          discharge_string_dec.
          rewrite H0.
          simpl.
          mychs.
          econstructor 1 with (ArbiterVal := true) (FreeListImplRegs :=
                                                      doUpdRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) true) :: news0 ++ news2) FreeListImplRegs).
          {

            rewrite stripIrrelevantUpd; [> | solve[solve_leftover_Ins FreeListImplRegs]].
            symmetry.
            eapply getKindAttr_doUpdRegs_app; solve[solve_leftover_Ins FreeListImplRegs] || admit.
          }
          {
            trivial.
          }
          {
            discharge_string_dec.
            reflexivity.
          }
          {
            try rewrite stripIrrelevantUpd; [> | solve[solve_leftover_Ins FreeListImplRegs]].
            simpl.
            constructor.
            intro.
            eapply inFstGetKindAttrIffInFst in H2.
            erewrite <-getKindAttr_doUpdRegs_app in H2.
            solve_leftover_Ins FreeListImplRegs.
            solve_leftover_Ins FreeListImplRegs.
            admit.
            admit.
            {
              eapply NoDupMapFstGetKindAttr.
              erewrite <-getKindAttr_doUpdRegs_app.
              eapply NoDupMapFstGetKindAttr.
              solve_leftover_Ins FreeListImplRegs. solve_leftover_Ins FreeListImplRegs.
              admit. admit.
            }
          }
          {
            eapply NoDupMapFstGetKindAttr.
            erewrite stripIrrelevantUpd.
            simpl getKindAttr at 1.
            erewrite <-getKindAttr_doUpdRegs.
            all: try solve[solve_leftover_Ins FreeListSpecRegs].
            solve_leftover_Ins FreeListSpecRegs. 
            econstructor.
            intro. eapply H11.
            admit.
            finisher.
            eapply NoDupMapFstGetKindAttr.
            eauto.
            admit.
          }
          {
            admit.
          }
        }
        {
          mychs.
          repeat discharge_SemAction; finisher; solve_leftover_Ins FreeListImplRegs.
        }
        {
          mychs.
          econstructor 1 with (ArbiterVal := true) (FreeListImplRegs :=
                                                      doUpdRegs ((ArbiterName, existT (fullType type) (SyntaxKind Bool) true) :: news0 ++ news2) FreeListImplRegs).
          {
            rewrite stripIrrelevantUpd.
            symmetry.
            eapply getKindAttr_doUpdRegs_app; solve[solve_leftover_Ins FreeListImplRegs] || admit.
            solve_leftover_Ins FreeListImplRegs.
          }
          {
            simpl; discharge_string_dec.
            f_equal.
            rewrite ?app_nil_r, ?app_nil_l.
            reflexivity.
          }
          {
            repeat rewrite app_nil_r, app_nil_l.
            f_equal.
            simpl in H0.
            rewrite H0.
            simpl.
            discharge_string_dec.
            auto.
          }
          {
            discharge_string_dec.
            solve_leftover_Ins FreeListImplRegs.
          }
          {
            repeat rewrite app_nil_r, app_nil_l.
            simpl.
            simpl in H0.
            rewrite H0.
            simpl.
            discharge_string_dec.
            simpl.
            erewrite stripIrrelevantUpd.
            econstructor.
            -
              intro.
              eapply inFstGetKindAttrIffInFst in H11.
              erewrite <-getKindAttr_doUpdRegs in H11.
              all: solve[solve_leftover_Ins FreeListSpecRegs] || admit.
            -
              eapply InGetKindAttr in H1.
              eapply NoDupMapFstGetKindAttr.
              erewrite <-getKindAttr_doUpdRegs.
              eapply NoDupMapFstGetKindAttr.
              auto.
              solve_leftover_Ins FreeListSpecRegs.
              solve_leftover_Ins FreeListSpecRegs.
              intros.
              simpl in H10.
              destruct H10; intuition auto.
              inversion H10.
              subst.
              auto.
              all: solve[solve_leftover_Ins FreeListSpecRegs] || admit.
            -
              solve_leftover_Ins FreeListSpecRegs.
          }
          {
            simpl.
            simpl in H0.
            do 2 try rewrite stripIrrelevantUpd; try first [solve [solve_leftover_Ins FreeListSpecRegs] | solve[solve_leftover_Ins FreeListImplRegs]].
          }
        }
        {
          mychs.
          admit.
        }
        {
          repeat rewrite app_nil_r, app_nil_l.
          simpl.

          discharge_string_dec.
          simpl.

          do 2 try rewrite stripIrrelevantUpd; try first [solve [solve_leftover_Ins FreeListSpecRegs] | solve[solve_leftover_Ins FreeListImplRegs]].
          repeat discharge_string_dec.
          econstructor 1 with (ArbiterVal := true) (FreeListImplRegs := doUpdRegs (news0 ++ news2) FreeListImplRegs)
                              (FreeListSpecRegs := doUpdRegs
                                                     [(ArrayName,
                                                       existT (fullType type) (SyntaxKind (Array len Bool))
                                                              (fun i : t len =>
                                                                 if getBool (weq rv1 $(proj1_sig (to_nat i)))
                                                                 then
                                                                   if
                                                                     match Compare_dec.lt_dec # (rv1) len with
                                                                     | left pf => fun fv : t len -> bool => fv (of_nat_lt pf)
                                                                     | right _ => fun _ : t len -> bool => false
                                                                     end rv0
                                                                   then
                                                                     match Compare_dec.lt_dec # (rv1) len with
                                                                     | left pf => fun fv : t len -> bool => fv (of_nat_lt pf)
                                                                     | right _ => fun _ : t len -> bool => false
                                                                     end rv0
                                                                   else true
                                                                 else rv0 i))] FreeListSpecRegs).
          symmetry. eapply getKindAttr_doUpdRegs_app.
          solve_leftover_Ins FreeListImplRegs.
          admit.
          admit.
          auto.
          f_equal.
          simpl.
          all: admit.
        }
      }
      { admit. }
      { admit. }
    }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    Unshelve.
    all: repeat econstructor.
    
  Admitted.

End Proofs.

*)
