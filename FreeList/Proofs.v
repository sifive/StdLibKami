(* Inductive Expr := *)
(* | One : Expr *)
(* | Mul : Expr -> Expr -> Expr *)
(* | Add : Expr -> Expr -> Expr *)
(* | Opp : Expr -> Expr. *)

(* (* Expr is defined *) *)
(* (* Expr_rect is defined *) *)
(* (* Expr_ind is defined *) *)
(* (* Expr_rec is defined *) *)

(* Declare Custom Entry expr. *)
(* Notation "[ e ]" := e (e custom expr at level 2). *)

(* (* Setting notation at level 0. *) *)

(* Notation " 1 " := One (in custom expr at level 0). *)
(* Notation "x * y" := (Mul x y) (in custom expr at level 1, left associativity). *)
(* Notation "x + y" := (Add x y) (in custom expr at level 2, left associativity). *)
(* Notation "{| x , y |}" := (Mul x y) (in custom expr at level 2, left associativity). *)


(* Notation "( x )" := x (in custom expr, x at level 2). *)

(* (* Setting notation at level 0. *) *)

(* Notation "- y" := (Opp y) (in custom expr at level 1). *)

(* Notation "x - y" := (Add x (Opp y)) (in custom expr at level 2). *)

(* (* Setting notation at level 0. *) *)

(* Notation "{ x }" := x (in custom expr, x constr). *)

(* (* Setting notation at level 0. *) *)

(* Notation "x" := x (in custom expr at level 0, x ident). *)
(* Axiom f : nat -> Expr. *)

(* (* f is declared *) *)

(* Unset Printing Notations. *)
(* Check fun x y => [{|x, y |}]. *)

(* Check fun x y z => [1 + y * z + {f (x + 1)}]. *)
(* Unset Printing Notations. *)
(* Check fun x y z => [1 + y * z + {f (x + 1)}]. *)
(* Check fun x y => [x + y * x + y]. *)
(* Check fun x y z => [- 1 - x + y * z]. *)

(* Set Printing Notations. *)
(* Check (fun x y z => (Add (Add (Add (Opp One) (Opp (Mul y z))) (f x))) (f 1 )). *)

(* Definition testing_notations x y z := *)
(*   [x + y * z + - 1]. *)

(* Print testing_notations. *)

(* Inductive BinOps := *)
(* | BinEq : Expr -> Expr -> BinOps *)
(* | BinLt : Expr -> Expr -> BinOps *)
(* | BinGt : Expr -> Expr -> BinOps. *)

(* Declare Custom Entry binexpr. *)
(* Notation "[| b |]" := b (b custom binexpr at level 4, no associativity). *)

(* (* Notation "x = y" := (BinEq x y) (in custom binexpr at level 4, no associativity, x custom expr at level 2, y custom expr at level 2). *) *)
(* (* Notation "x < y" := (BinLt x y) (in custom binexpr at level 4, no associativity, x custom expr at level 2, y custom expr at level 2). *) *)
(* (* Notation "x > y" := (BinGt x y) (in custom binexpr at level 4, no associativity, x custom expr at level 2, y custom expr at level 2). *) *)

(* Notation "x = y" := (BinEq x y) (in custom binexpr at level 4, no associativity). *)
(* Notation "x < y" := (BinLt x y) (in custom binexpr at level 4, no associativity). *)
(* Notation "x > y" := (BinGt x y) (in custom binexpr at level 4, no associativity). *)

(* Notation " x " := x (in custom binexpr at level 0, x custom expr at level 2). *)

(* Check fun w x y z => [|x + y > y * z + {f w}|]. *)
(* Check fun x y => [| x + y = 1 - x |]. *)
(* Check fun x y z => [|x + y * z - 1|]. *)


(* (* fun (x : nat) (y z : Expr) => [~ 1 + y z + {f x}] *) *)
(* (*      : nat -> Expr -> Expr -> Expr *) *)

(* Unset Printing Notations. *)
(* Check fun x y z => [-1 + y * z + {f x}]. *)

(* (* fun (x : nat) (y z : Expr) => Add (Add (Opp One) (Mul y z)) (f x) *) *)
(* (*      : forall (_ : nat) (_ : Expr) (_ : Expr), Expr *) *)

(* Set Printing Notations. *)
(* Check fun e => match e with *)
(* | [1 + 1] => [|1|] *)
(* | [x * y + z] => [x + y * z] *)
(* | y => [y + e] *)
(* end. *)

(* (* fun e : Expr => *) *)
(* (* match e with *) *)
(* (* | [1 + 1] => [1] *) *)
(* (* | [x y + z] => [x + y z] *) *)
(* (* | _ => [e + e] *) *)
(* (* end *) *)
(* (* : Expr -> Expr *) *)


(* Check fun x y z => [~1 + y z + {f x}]. *)

(* Definition foo := [~1 + {f 1} 1]. *)
(* Print foo. *)
(* Print Custom Grammar expr. *)



Require Import Kami.All.
Require Import StdLibKami.FreeList.Spec.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.FreeList.Array.
Require Import Coq.Logic.EqdepFacts.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxTactics.
Require Import Kami.GallinaModules.AuxLemmas.

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
  (*   - hyp_consumer1. *)
  (*     + goal_consumer. *)
  (*       my_simpl_solver. *)
  (*       goal_consumer. *)
  (*       my_simpl_solver. *)
  (*       repeat goal_consumer. *)
  (*       3 : { reflexivity. *)
  (*       } *)
  (*       3 : auto. *)
  (*       3 : auto. *)
  (*       3 : auto. *)
  (*       unfold Array.arrayRegName. *)
  (*       unfold Spec.arrayRegName. *)
  (*       auto. *)
End Proofs.
