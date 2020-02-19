Require Import Kami.All.
Require Import StdLibKami.FreeList.Spec.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.FreeList.Array.
Require Import Coq.Logic.EqdepFacts.
Require Import StdLibKami.KamiCorrectness.

Record FreeListCorrect {FLParams} (imp spec: @FreeList FLParams): Type :=
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

Section Proofs.
  Context `{Params : FreeListParams}.

  Definition spFreeList := @specFreeList Params.
  Definition arrFreeList := @arrayFreeList Params.
    
  Record myArrayFreeListR (o_i o_s : RegsT) : Prop :=
    {
      LocalReg : RegT;
      ArrayVal : Fin.t Array.len -> bool;
      LocalRegVal : LocalReg = (Array.arrayRegName, existT _ (SyntaxKind (Array Array.len Bool)) ArrayVal);
      Ho_iCorrect : o_i = [LocalReg];
      Ho_sCorrect : o_s = [LocalReg];
      Ho_iNoDup : NoDup (map fst o_i);
      Ho_sNoDup : NoDup (map fst o_s)
    }.
  
  Ltac Record_destruct :=
    match goal with
    | [ H : myArrayFreeListR _ _ |- _] => destruct H
    end.

  (* Goal FreeListCorrect arrFreeList spFreeList. *)
  (*   econstructor 1 with (freeListR := myArrayFreeListR) *)
  (*                       (freeListRegs := [(Array.arrayRegName, SyntaxKind (Array Array.len Bool))]). *)
  (*   all : *)
  (*     intros *)
  (*     ; unfold EffectfulRelation, EffectlessRelation, ActionWb *)
  (*     ; intros *)
  (*     ; try Record_destruct *)
  (*     ; try (destruct LocalReg; inv LocalRegVal) *)
  (*     ; unfold nextToAlloc, alloc, free, arrayFreeList, specFreeList, arrFreeList, spFreeList, *)
  (*       arrayFreeList, specFreeList, Array.nextToAlloc, Spec.nextToAlloc in *. *)
  (*   unfold in *. *)
  (*   unfold arrayFreeList in *. *)
  (*   unfold Array.nextToAlloc in *. *)

End Proofs.
