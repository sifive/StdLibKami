(* Implements the Pseudo Least Recently Used Algorithm. *)
Require Import Kami.AllNotations.
Require Import StdLibKami.ReplacementPolicy.Ifc.

Section lru.
  Open Scope kami_expr.
  Open Scope kami_action.

  (*
    the number of data registers.
    Note: should be of the form 2^n for some n.
  *)
  Variable num : nat.

  (* the name of the register that stores the path of the least recently used data register *)
  Variable stateRegName : string.

  (*
    Note: the number of internal nodes in the balanced binary tree is [num - 1].
  *)
  Definition stateWidth := (num - 1)%nat.

  (* represents the state of the Lru unit - i.e. the value of each node within the state tree. *)
  Definition State := Array stateWidth Bool.

  (*
    Note: the total number nodes and leaves in the tree is [2*num - 1].
  *)
  Definition treeNodeWidth := Nat.log2_up (2 * num - 1)%nat.

  Definition TreeNodeIndex := Bit treeNodeWidth.

  Definition IndexWidth := Nat.log2_up num.

  Definition Index := Bit IndexWidth.

  Section ty.
    Variable ty : Kind -> Type.

    Definition treeNodeIndex
      (treeNode : TreeNodeIndex @# ty)
      :  Index @# ty
      := ~(ZeroExtendTruncLsb IndexWidth treeNode + $1).

    Fixpoint getVictimAux
      (depth : nat)
      (state : State @# ty)
      (treeNode : TreeNodeIndex @# ty)
      :  Index ## ty
      := LETC index : Index <- treeNodeIndex treeNode;
         LETC direction : Bool <- state@[#index];
         match depth with
         | 0
           => RetE #index
         | S depth'
           => LETE result
                :  Index
                <- getVictimAux depth' state
                     (IF #direction
                       then (treeNode << ($1 : Bit 1 @# ty)) | $1 (* left child's treeNode *)
                       else (treeNode << ($1 : Bit 1 @# ty)));    (* right child's treeNode *)
              RetE
                (IF #index >= $(num - 1)
                  then #index
                  else #result)
         end.

    (* The maximum depth of the balanced tree. *)
    Definition Depth := Nat.log2_up num.

    (* The root node treeNode. *)
    Definition rootTreeNodeIndex : TreeNodeIndex @# ty := $$(wones treeNodeWidth) << ($1 : Bit 1 @# ty).

    (* Returns the index of the least recently used register *)
    Definition getVictim'
      :  ActionT ty Index
      := Read state : State <- stateRegName;
         convertLetExprSyntax_ActionT
           (getVictimAux Depth #state rootTreeNodeIndex).

    Definition indexTreeNodeIndex
      (index : Index @# ty)
      :  TreeNodeIndex @# ty
      := (~ (ZeroExtendTruncLsb treeNodeWidth index)) - $1.

    (* Note: treeNode must not be the root or the dual of the root - i.e. treeNodeIndex treeNode != 0 *)
    Definition parentTreeNodeIndex
      (treeNode : TreeNodeIndex @# ty)
      :  TreeNodeIndex @# ty
      := OneExtendTruncLsb treeNodeWidth
           (ZeroExtendTruncMsb (treeNodeWidth - 1) treeNode).

    Fixpoint accessAuxRec
      (maxDepth : nat)
      (state : State @# ty)
      (treeNode : TreeNodeIndex @# ty)
      (direction : Bool @# ty)
      :  State ## ty
      := match maxDepth with
         | 0 => RetE state (* impossible case - bounding recursion. *)
         | S depth
           => LETC index : Index <- treeNodeIndex treeNode;
              LETC nextState : State <- state@[#index <- direction];
              LETE result : State
                <- accessAuxRec depth #nextState (parentTreeNodeIndex treeNode)
                     (ZeroExtendTruncLsb 1 treeNode == $0);
              RetE
                (IF treeNode == rootTreeNodeIndex
                  then #nextState
                  else #result)
         end.

    Definition accessAux
      (state : State @# ty)
      (index : Index @# ty)
      :  State ## ty
      := LETC rawTreeNodeIndex : TreeNodeIndex <- indexTreeNodeIndex index;
         LETC treeNode : TreeNodeIndex
           <- IF #rawTreeNodeIndex == rootTreeNodeIndex
               then #rawTreeNodeIndex << ($1 : Bit 1 @# ty) >> ($1 : Bit 1 @# ty) (* set msb to 0 *)
               else #rawTreeNodeIndex;
         accessAuxRec Depth state
           (parentTreeNodeIndex #treeNode)
           (ZeroExtendTruncLsb 1 #treeNode == $0).

    (* updates the least recently used data to point away from the given register. *)
    Definition access'
      (index : Index @# ty)
      :  ActionT ty Void
      := Read state : State <- stateRegName;
         LETA result : State <- convertLetExprSyntax_ActionT (accessAux #state index);
         Write stateRegName : State <- #result;
         Retv.

  End ty.

  Close Scope kami_action.
  Close Scope kami_expr.
End lru.

Section interface.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class PseudoLruParams
    := {
      stateRegName : string;
      num : nat
    }.

  Section instance.
    Context `{psuedoLruParams : PseudoLruParams}.

    Definition PsuedoLru
      :  ReplacementPolicy num
      := {|
           getVictim := fun ty => getVictim' num stateRegName ty;
           access := fun ty index => access' stateRegName index
         |}.

  End instance.

  Close Scope kami_action.
  Close Scope kami_expr.
End interface.

Section tests.

  Open Scope kami_expr.

  Local Definition T := Const type true.
  Local Definition F := Const type false.

  Definition testGetVictim
    (num : nat)
    (state : State num @# type)
    (expected : word (IndexWidth num))
    :  Prop
    := (evalLetExpr
         (LETE result
           : Index num
           <- getVictimAux
                (Depth num)
                state
                (rootTreeNodeIndex num type);
          RetE (Var type (SyntaxKind _) result))) =
        expected.

  Goal testGetVictim (num := 3) (ARRAY {T; T}) $3. Proof ltac:(reflexivity). 
  Goal testGetVictim (num := 3) (ARRAY {T; F}) $0. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 3) (ARRAY {F; T}) $2. Proof ltac:(reflexivity).

  Goal testGetVictim (num := 6) (ARRAY {T; T; T; T; T}) $7. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {F; T; T; T; T}) $5. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {F; T; F; T; T}) $6. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {T; F; T; T; F}) $2. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {T; F; T; T; T}) $1. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 6) (ARRAY {T; T; T; F; T}) $0. Proof ltac:(reflexivity).

  Goal testGetVictim (num := 7) (ARRAY {T; T; T; T; T; T}) $7. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {T; T; T; F; T; T}) $0. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {T; F; F; T; T; T}) $1. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {T; F; T; T; F; T}) $2. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {F; T; T; T; T; T}) $3. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {F; T; T; T; T; F}) $4. Proof ltac:(reflexivity).
  Goal testGetVictim (num := 7) (ARRAY {F; T; F; T; T; T}) $6. Proof ltac:(reflexivity).

  Goal (evalExpr (indexTreeNodeIndex (num := 5) (Const type (natToWord _ 7)))) = natToWord _ 7. Proof. reflexivity. Qed.
  Goal (evalExpr (indexTreeNodeIndex (num := 5) (Const type (natToWord _ 4)))) = 4'b"1010". Proof. reflexivity. Qed.
  Goal (evalExpr (parentTreeNodeIndex (num := 5) (Const type (4'b"1010")))) = 4'b"1101". Proof. reflexivity. Qed.
  Goal (evalExpr (parentTreeNodeIndex (num := 5) (Const type (4'b"1001")))) = 4'b"1100". Proof. reflexivity. Qed.
  Goal (evalExpr (parentTreeNodeIndex (num := 5) (Const type (4'b"0110")))) = 4'b"1011". Proof. reflexivity. Qed.
  Goal (evalExpr (parentTreeNodeIndex (num := 5) (Const type (4'b"0111")))) = 4'b"1011". Proof. reflexivity. Qed.

  Definition evalArray
    (k : Kind)
    (n : nat)
    :  Array n k ## type -> list (type k)
    := match n return Array n k ## type -> list (type k) with
       | 0 => fun _ => []
       | S n
         => nat_rect
              (fun m : nat
                => m < (S n) -> Array (S n) k ## type -> list (type k))
              (fun (H : 0 < (S n)) xs
                => [(evalLetExpr xs) (Fin.of_nat_lt H)])
              (fun m F (H : S m < (S n)) xs
                => (F (Nat.lt_succ_l m (S n) H) xs) ++
                   [(evalLetExpr xs) (Fin.of_nat_lt H)])
              n (Nat.lt_succ_diag_r n)
      end%nat.

  Definition testAccess
    (num : nat)
    (state : State num @# type)
    (index : Index num @# type)
    (expected : list bool)
    :  Prop
    := evalArray (accessAux (num := num) state index) = expected.

  Goal testAccess (num := 2) (ARRAY {T}) (Const type (1'b"0")) [true]. Proof ltac:(reflexivity).
  Goal testAccess (num := 2) (ARRAY {T}) (Const type (1'b"1")) [false]. Proof ltac:(reflexivity).
  Goal testAccess (num := 3) (ARRAY {T; T}) (Const type (2'b"11")) [false; false]. Proof ltac:(reflexivity).
  Goal testAccess (num := 3) (ARRAY {T; T}) (Const type (2'b"00")) [false; true]. Proof ltac:(reflexivity).
  Goal testAccess (num := 3) (ARRAY {T; T}) (Const type (2'b"10")) [true; true]. Proof ltac:(reflexivity).

  Close Scope kami_expr.

End tests.
