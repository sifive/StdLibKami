(* Implements the Pseudo Least Recently Used Algorithm. *)
Require Import Wf.
Require Import Wf_nat.
Require Import Kami.AllNotations.

Section lru.
  Open Scope kami_expr.
  Open Scope kami_action.

  (* the number of data registers *)
  Variable num : nat.

 (* the type of data stored in the registers *)
  Variable Data : Kind.

  (* the name of the register that stores the path of the least recently used data register *)
  Variable lruRegName : string.

  (*
    Note: the number of internal nodes in the balanced binary tree is [num - 1].
  *)
  Definition lruWidth := (num - 1)%nat.

  Definition Lru := Array lruWidth Bool.

  (*
    Note: the total number nodes and leaves in the tree is [2*num - 1].
  *)
  Definition indexWidth := Nat.log2_up (2 * num + 1)%nat.

  Definition Index := Bit indexWidth.

  Definition regIndexWidth := Nat.log2_up num.

  Definition RegIndex := Bit regIndexWidth.

  Section ty.
    Variable ty : Kind -> Type.

    Definition regIndex
      (index : Index @# ty)
      :  RegIndex @# ty
      := ~(ZeroExtendTruncLsb regIndexWidth index + $1).

    Fixpoint getVictimAux
      (depth : nat)
      (lru : Lru @# ty)
      (index : Index @# ty)
      :  Pair RegIndex Lru ## ty
      := LETC reg : RegIndex <- regIndex index;
         LETC dir : Bool <- lru@[ZeroExtendTruncLsb lruWidth #reg];
         match depth with
         | 0
           => RetE (STRUCT {
                "fst" ::= #reg;
                "snd" ::= lru
                } : Pair RegIndex Lru @# ty)
         | S depth'
           => LETE result
                :  Pair RegIndex Lru
                <- getVictimAux depth'
                     (lru@[#reg <- !#dir])
                     (IF #dir
                       then (index << ($1 : Bit 1 @# ty)) | $1
                       else (index << ($1 : Bit 1 @# ty)));
              RetE
                (IF #reg >= $(num - 1)
                  then
                    (STRUCT {
                       "fst" ::= #reg;
                       "snd" ::= lru
                     } : Pair RegIndex Lru @# ty)
                  else #result)
         end.

    (* The maximum depth of the balanced tree. *)
    Definition depth := Nat.log2_up num.

    (* The initial index into the binary tree. *)
    Definition initIndex : Index @# ty := $$(wones indexWidth) << ($1 : Bit 1 @# ty).

    (* Returns the index of the least recently used register *)
    Definition getVictim
      :  ActionT ty RegIndex
      := Read lru : Lru <- lruRegName;
         LETA result
           :  Pair RegIndex Lru
           <- convertLetExprSyntax_ActionT
                (getVictimAux depth #lru initIndex);
         Write lruRegName : Lru <- #result @% "snd";
         Ret (#result @% "fst").

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.
End lru.

Section tests.

  Open Scope kami_expr.

  Local Definition T := Const type true.
  Local Definition F := Const type false.

  Definition test
    (num : nat)
    (lru : Lru num @# type)
    (expected : word (regIndexWidth num)) : Prop
    := (evalLetExpr
         (LETE result
           : Pair (RegIndex num) (Lru num)
           <- getVictimAux
                (depth num)
                lru
                (initIndex num type);
          RetE ((Var type (SyntaxKind _) result) @% "fst"))) =
        expected.

  Goal test (num := 3) (ARRAY {T; T}) $3. Proof ltac:(reflexivity). 
  Goal test (num := 3) (ARRAY {T; F}) $0. Proof ltac:(reflexivity).
  Goal test (num := 3) (ARRAY {F; T}) $2. Proof ltac:(reflexivity).

  Goal test (num := 6) (ARRAY {T; T; T; T; T}) $7. Proof ltac:(reflexivity).
  Goal test (num := 6) (ARRAY {F; T; T; T; T}) $5. Proof ltac:(reflexivity).
  Goal test (num := 6) (ARRAY {F; T; F; T; T}) $6. Proof ltac:(reflexivity).
  Goal test (num := 6) (ARRAY {T; F; T; T; F}) $2. Proof ltac:(reflexivity).
  Goal test (num := 6) (ARRAY {T; F; T; T; T}) $1. Proof ltac:(reflexivity).
  Goal test (num := 6) (ARRAY {T; T; T; F; T}) $0. Proof ltac:(reflexivity).

  Goal test (num := 7) (ARRAY {T; T; T; T; T; T}) $7. Proof ltac:(reflexivity).
  Goal test (num := 7) (ARRAY {T; T; T; F; T; T}) $0. Proof ltac:(reflexivity).
  Goal test (num := 7) (ARRAY {T; F; F; T; T; T}) $1. Proof ltac:(reflexivity).
  Goal test (num := 7) (ARRAY {T; F; T; T; F; T}) $2. Proof ltac:(reflexivity).
  Goal test (num := 7) (ARRAY {F; T; T; T; T; T}) $3. Proof ltac:(reflexivity).
  Goal test (num := 7) (ARRAY {F; T; T; T; T; F}) $4. Proof ltac:(reflexivity).
  Goal test (num := 7) (ARRAY {F; T; F; T; T; T}) $6. Proof ltac:(reflexivity).

  Close Scope kami_expr.

End tests.
