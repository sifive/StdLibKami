(* Implements the Pseudo Least Recently Used Algorithm. *)
Require Import Kami.AllNotations.
Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import ZArith.

Section lru.
  Class PseudoLruParams := { stateRegName : string;
                             num : nat
                           }.

  Variable params: PseudoLruParams.
  
  Definition State := Array (num - 1) Bool.
  Definition IndexWidth := Nat.log2_up num.
  Definition Index := Bit IndexWidth.
  Definition PathWidth := IndexWidth.
  Definition Path := Index.
  Definition TreeIndexWidth := IndexWidth.
  Definition TreeIndex := Index.
  Definition Depth := IndexWidth.
    
  Section ty.
    Variable ty : Kind -> Type.
    
    Definition leftOverNum := num - Nat.pow 2 (Nat.log2 num).
    Definition twiceLeftOverNum := 2*leftOverNum.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition mul2 n (v: Bit n @# ty) := (v << ($1: Bit 1 @# ty)).
    Definition div2 n (v: Bit n @# ty) := (v >> ($1: Bit 1 @# ty)). 
    Definition mod2 n (v: Bit n @# ty) := (v & $1).

    Definition getPathFromIndex (i: Index @# ty) := match leftOverNum with
                                                    | 0 => i
                                                    | _ => (IF i < $twiceLeftOverNum
                                                            then i
                                                            else mul2 (i - $leftOverNum))
                                                    end.

    Definition getIndexFromPath (p: Path @# ty) := match leftOverNum with
                                                   | 0 => p
                                                   | _ => (IF p < $twiceLeftOverNum
                                                           then p
                                                           else div2 p + $leftOverNum)
                                                   end.

    Section state.
      Variable state: State @# ty.
      Fixpoint getVictimAux (depth: nat) (i: TreeIndex @# ty) (p: Path @# ty): Path ## ty :=
        match depth with
        | 0 => RetE p
        | S m => (IfE i >= $(num-1)
                  then RetE (mul2 p)
                  else (LETC direction : Bool <- state@[i];
                          LETC newIndex : TreeIndex <- mul2 i + IF #direction then $2 else $1;
                          LETC newPath : Path <- mul2 p | IF #direction then $1 else $0;
                          LETE retPath : Path <- (getVictimAux m #newIndex #newPath);
                          RetE #retPath) as retPath;
                    RetE #retPath)
        end.
    End state.

    Section path.
      Variable path: Path @# ty.
      Local Definition pathToArray: Array PathWidth Bool @# ty := unpack (Array PathWidth Bool) match eq_sym (Nat.mul_1_r PathWidth) in _ = Y return Bit Y @# ty with
                                                                                                | eq_refl => path
                                                                                                end.
      Fixpoint accessAux (depth: nat) (i: TreeIndex @# ty) (s: State @# ty): State ## ty :=
        match depth with
        | 0 => RetE s
        | S m => (IfE i >= $(num-1)
                  then RetE s
                  else (LETC direction: Bool <- (* pathToArray@[$$ (natToWord (Nat.log2_up PathWidth) m)] *) ((path >> ($m: Bit PathWidth @# ty)) & $1) == $1;
                          LETC newIndex : TreeIndex <- mul2 i + (IF #direction then $2 else $1);
                          LETC newState : State <- s@[i <- !#direction];
                          LETE retState : State <- (accessAux m #newIndex #newState);
                          RetE #retState) as retState;
                    RetE #retState)
        end.
    End path.
  End ty.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  
  Definition PseudoLru
    :  ReplacementPolicy num
    := {|
        getVictim := (fun ty =>
                        Read state : State <- stateRegName;
                          LETA path : Path <- convertLetExprSyntax_ActionT
                                           (getVictimAux #state Depth $0 $0);
                          Ret (getIndexFromPath #path));
        access := (fun ty index =>
                     Read state : State <- stateRegName;
                       LETA result : State <- convertLetExprSyntax_ActionT (accessAux (getPathFromIndex index) Depth $0 #state);
                       Write stateRegName : State <- #result;
                       Retv)
      |}.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End lru.

Section tests.

  (* Transparent wlt_dec. *)
  Open Scope kami_expr.

  Local Notation L := (Const type false).
  Local Notation R := (Const type true).

  Definition testGetVictim (num : nat)
    := let params := {| num := num; stateRegName := "test" |} in
       fun (state: State params @# type) (expected : word (IndexWidth params)) =>
         (evalLetExpr (LETE path : Path params <- getVictimAux state (Depth params) $0 $0;
                         RetE (getIndexFromPath (Var _ (SyntaxKind _) path))) = expected).

  Goal testGetVictim (num := 3) (ARRAY {R; R}) (zToWord _ 2). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 3) (ARRAY {R; L}) (zToWord _ 2). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 3) (ARRAY {L; R}) (zToWord _ 1). Proof. reflexivity. Qed.

  Goal testGetVictim (num := 6) (ARRAY {R; R; R; R; R}) (zToWord _ 5). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {L; R; R; R; R}) (zToWord _ 3). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {L; R; L; R; R}) (zToWord _ 3). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {R; L; R; R; L}) (zToWord _ 5). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {R; L; R; R; R}) (zToWord _ 5). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {R; R; R; L; R}) (zToWord _ 5). Proof. reflexivity. Qed.
  
  Goal testGetVictim (num := 7) (ARRAY {R; R; R; R; R; R}) (zToWord _ 6). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {R; R; R; L; R; R}) (zToWord _ 6). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {R; L; L; R; R; R}) (zToWord _ 5). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {R; L; R; R; L; R}) (zToWord _ 6). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {L; R; R; R; R; R}) (zToWord _ 3). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {L; R; R; R; R; L}) (zToWord _ 3). Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {L; R; L; R; R; R}) (zToWord _ 3). Proof. reflexivity. Qed.

  Definition evalArray
    (k : Kind)
    (n : nat)
    (arr: Array n k ## type)
    :  list (type k)
    := map (evalLetExpr arr) (getFins n).

  Definition testAccess (num : nat) :=
    let params := {| num := num; stateRegName := "test" |} in
    fun (state: State params @# type) (index: Index params @# type) (expected : list bool) =>
      evalArray (accessAux (getPathFromIndex index) (Depth params) $0 state) = expected.
  
  Goal testAccess (num := 2) (ARRAY {R}) (Const type (1'b"0")) [true].
  Proof. cbv. repeat destruct weq; try inversion e0; auto. Qed.
  Goal testAccess (num := 2) (ARRAY {R}) (Const type (1'b"1")) [false].
  Proof. cbv. repeat destruct weq; try contradiction; auto. Qed.
  
  (* Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"01")) [true; false].
  Proof. reflexivity. Qed.
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"00")) [true; true].
  Proof. reflexivity. Qed.
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"10")) [false; true]. Proof. reflexivity. Qed.
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"11")) [true; true]. Proof. reflexivity. Qed.  *)

  Close Scope kami_expr.
  Opaque wlt_dec.
End tests.
