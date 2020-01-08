Require Import Kami.All.
Require Import StdLibKami.Arbiter.AuxLemmas.
Require Import StdLibKami.KamiCorrectness.

(* subst, but also rewrites with arbitrary equalities *)
Ltac mySubst :=
  progress first [subst |
                  match goal with
                  | [H : _ = _ |- _] =>
                    try rewrite H in *; clear H; subst
                  end].

(* Shouldn't be called explicitly *)
Ltac expand_semaction :=
  lazymatch goal with
  | [|- SemAction _ ?a _ _ _ _] =>
           eapply SemActionExpandRegs;
           [> repeat match goal with
                     | [H: SemAction _ a _ _ _ _ |- _] => solve[eapply H]
                     end | idtac | idtac ]
  end.

(* Handles some trivial goals, potentially unifying evars along the way. *)
Ltac finisher :=
  repeat match goal with
         | [H: In _ [] |- _] => solve [inversion H]
         | [H: SubList _ _ |- SubList _ _ ] => solve [eapply H]
         | [H: SemAction _ _ _ _ _ _ |- SemAction _ _ _ _ _ _] => eapply H
         | [|- In _ (getKindAttr _) ] => eapply InGetKindAttr
         | [ H: forall _, In _ _ -> In _ _ |- _ ] => solve [eapply H]
         | [H: In _ _ |- In _ _] => solve [eapply H]
         | _ => progress mySubst
         | _ => progress (autorewrite with cor_db in *; simpl in *; auto)
         end.

(* Finishes goals raised by application of lemmas relating to SubList.
   Shouldn't be called explicitly. *)
Ltac sublist_finisher SubmodImplRegs :=
  match goal with
  | |- ~ In (?name,_) _ => assert (~ In name (map fst SubmodImplRegs)); intro
  | [H: NoDup _ |- False] => inversion H; clear H; solve[intuition]
  | [H: ~ In _ _ |- False] => eapply H
  | [H: map (fun x : RegT => (let (x0, _) := x in x0, let (a, _) := let (_, y) := x in y in a)) _ = map (fun x : RegT => (let (x0, _) := x in x0, let (a, _) := let (_, y) := x in y in a)) _ |- _] => 
    erewrite <-(getKindAttrEqImpFstEq _ _ H)
  | |- In _ (map fst _) => eapply inImpInFst; solve[finisher]
  | |- _  => solve[finisher]
  end.

(* Solves Sublist goals about "submodule" implementation registers *)
Ltac discharge_SubList SubmodImplRegs :=
  match goal with
  | |- SubList _ SubmodImplRegs => solve[eapply SubList_transitive; repeat sublist_finisher SubmodImplRegs; eapply SubList_Strengthen; repeat sublist_finisher SubmodImplRegs]
  end.

(* Solves some List.In goals by making use of List.NoDup
   hypotheses. Should not be called explicitly. *)
Ltac solve_leftover_Ins SubmodImplRegs :=
  match goal with
  | [H: NoDup ?a |- _] =>
    match a with
    | context[SubmodImplRegs] => inversion H; intuition
    end
  end;
  repeat match goal with
         | [H: In _ _ |- _] => eapply inImpInFst in H
         | [H: In _ (map fst (getKindAttr SubmodImplRegs)) |- _] => eapply inFstGetKindAttrIffInFst in H; contradiction
         end;
  intuition auto.

Ltac noExtraGoals tac :=
  (let n := numgoals in
   tac;
   let n' := numgoals in
   guard n' = n).

