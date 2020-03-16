Require Import Kami.All.
Require Import StdLibKami.Arbiter.Impl.
Require Import StdLibKami.FreeList.Spec.
Require Import StdLibKami.Arbiter.Ifc.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.FreeList.Ifc.
Require Import Coq.Logic.EqdepFacts.
Require Import Kami.GallinaModules.Relations.


Record FreeListCorrect {len} (imp spec: @FreeList.Ifc.Ifc len): Type :=
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

Record ArbiterCorrect `{Arbiter.Ifc.Params} (imp spec: Arbiter.Ifc.Ifc): Type :=
  {
    arbiterRegs: list (Attribute FullKind);
    outerRegs : list (Attribute FullKind);
    arbiterR: RegsT -> RegsT -> Prop;
    sendReqCorrect: forall 
        (req : forall ty : Kind -> Type, ty OutReq -> ActionT ty (Maybe immResK)),
        (forall reqa, ActionWb outerRegs (@req type reqa)) ->
        forall cid creqa , EffectfulRelation arbiterR (@sendReq _ imp req cid type creqa) (@sendReq _ spec req cid type creqa);
    sendReqWb: forall 
        (req : forall ty : Kind -> Type, ty OutReq -> ActionT ty (Maybe immResK)),
        (forall reqa, ActionWb outerRegs (@req type reqa)) ->
        forall cid creqa, ActionWb arbiterRegs (@sendReq _ imp req cid type creqa);
    memCallbackCorrect:
        (forall (reqK resK : Kind) (ac : Client reqK resK) cr, ActionWb outerRegs (@clientHandleRes reqK resK ac type cr)) ->
        forall resp, EffectfulRelation arbiterR (@callback _ imp type resp) (@callback _ spec type resp);
    memCallbackWb: 
      (forall (reqK resK : Kind) (ac : Client reqK resK) cr, ActionWb outerRegs (@clientHandleRes reqK resK ac type cr)) ->
      forall resp, ActionWb arbiterRegs (@callback _ imp type resp);
    ruleCorrect: EffectfulRelation arbiterR (@arbiterResetRule _ imp type) (@arbiterResetRule _ spec type);
    ruleWb: ActionWb arbiterRegs (@arbiterResetRule _ imp type);
  }.

(*
Section Proofs.
  (** * Common parameters *)
  Context `{A: Arbiter.Impl.Params}.
  (*
  Context (memReq: forall ty, ty MemReq -> ActionT ty Bool).
  *)
  (** * Spec parameters *)
  Variable (ArrayName AlistName AlistRead AlistWrite : string).
  
(*  Definition specFreeListParams: FreeListParams := Build_FreeListParams transactionTagSz ArrayName.
  Definition specFreeList := (@specFreeList specFreeListParams).*)
  Variable (specFreeList implFreeList: @FreeList.Ifc.Ifc (@freeList _ A)).
  Variable (implFreeListCorrect: FreeListCorrect implFreeList specFreeList).
  Variable (outerRegs : list (Attribute FullKind)).
  Definition specParams: ArbiterImplParams := 
    {| Arbiter.Impl.freelist := specFreeList |}.
  
  (** * Impl parameters *)
  Definition implParams: ArbiterImplParams :=
    {| Arbiter.Impl.freelist := implFreeList |}.

  (** * The arbiter pseudo-modules involved in the correctness proof *)
  Definition specArbiter := @arbiterImpl A specParams.
  Definition implArbiter := @arbiterImpl A implParams.
  

  Record myArbiterR (freelistR: RegsT -> RegsT -> Prop) freelistRegs outerRegs (o_i o_s: RegsT): Prop :=
    {
      ArbiterVal: bool;
      LocalReg: RegT;
      OuterRegs: RegsT;
      LocalRegVal : LocalReg = (Impl.arbiterBusyRegName, existT (fullType type) (SyntaxKind Bool) ArbiterVal);
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
  
(* Both break down the user defined Arbiter relation *)
Ltac Record_construct :=
  match goal with
  | [ |- myArbiterR _ _ _ _ _ ] => econstructor
  end.

Ltac Record_destruct :=
  match goal with
  | [ H : myArbiterR _ _ _ _ _ |- _] => destruct H
  end.


Ltac goal_consumer1 :=
  repeat goal_split
  ; repeat goal_body
  ; repeat normal_solver
  ; repeat doUpdRegs_simpl
  ; repeat doUpdRegs_red
  ; repeat Record_construct
  ; repeat normal_solver
  ; repeat my_risky_solver
  ; repeat gka_doUpdReg_red
  ; repeat normal_solver.

  Goal ArbiterCorrect implArbiter specArbiter.
    destruct implFreeListCorrect.
    econstructor 1 with (arbiterR:= myArbiterR freeListR0 freeListRegs0 outerRegs)
                        (outerRegs := outerRegs)
                        (arbiterRegs := (Impl.arbiterBusyRegName, SyntaxKind Bool) :: freeListRegs0 ++ outerRegs).
    all :
    intros;
      unfold EffectfulRelation, ActionWb; intros
      ; try Record_destruct; try (destruct LocalReg; inv LocalRegVal);
        unfold sendReq, memCallback, arbiterRule,
        implArbiter, specArbiter, implParams, specParams,
        arbiterImpl, Impl.sendReq, Impl.nextToAlloc,
        Impl.alloc, Impl.memCallback, Impl.arbiterRule,
        Impl.free, alloc, free,
        nextToAlloc, freelist in *.
    - hyp_consumer1; goal_consumer1.
    - hyp_consumer1; extract_in_map; goal_consumer2.
    - hyp_consumer1.
      extract_gatherActions OuterRegs (nil : list RegT).
      hyp_consumer1.
      repeat my_simplifier.
      repeat normalize_sublist_l; repeat sublist_sol; repeat my_simpl_solver.
      repeat goal_consumer1.
    - hyp_consumer1.
      extract_gatherActions2' outerRegs (getKindAttr (nil : RegsT))
      ; hyp_consumer1
      ; extract_in_map'
      ; goal_consumer2.
      apply H18.
      goal_consumer1.
    - hyp_consumer1; goal_consumer1.
    - hyp_consumer1; extract_in_map'; goal_consumer2; eauto.
      Unshelve.
         all : clear; repeat econstructor.
         all : repeat (match goal with
                       |[ |- ?f ?K] => induction K; simpl; repeat econstructor; eauto
                       end).
  Qed.

  (* Inductive disj_union : list RegsT -> Prop := *)
  (* | disj_nil : disj_union nil *)
  (* | disj_cons newRegs newUnion oldUnion *)
  (*             (HDisjNewRegs : forall oldRegs, *)
  (*                 In oldRegs oldUnion -> *)
  (*                 DisjKey newRegs oldRegs) *)
  (*             (HNewUnion : newUnion = newRegs :: oldUnion): *)
  (*     disj_union newUnion. *)

  (* Definition partition_of (l1 : RegsT) (l2 : list RegsT) := *)
  (*   disj_union l2 /\ l1 = concat l2 *)
  
End Proofs.
*)
