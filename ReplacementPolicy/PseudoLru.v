(* Implements the Pseudo Least Recently Used Algorithm. *)
Require Import Kami.AllNotations.
Require Import StdLibKami.ReplacementPolicy.Ifc.

Section lru.
  Context {policyParams : PolicyParams}.

  Local Definition stateRegName := (StdLibKami.ReplacementPolicy.Ifc.name ++ ".state")%string.

  (* Variable params: PseudoLruParams. *)
  
  Local Definition State := Array (num - 1) Bool.
  Local Definition IndexWidth := Nat.log2_up num.
  Local Definition Index := Bit IndexWidth.
  Local Definition PathWidth := IndexWidth.
  Local Definition Path := Index.
  Local Definition TreeIndexWidth := IndexWidth.
  Local Definition TreeIndex := Index.
  Local Definition Depth := IndexWidth.
    
  Section ty.
    Variable ty : Kind -> Type.
    
    Local Definition leftOverNum := num - Nat.pow 2 (Nat.log2 num).
    Local Definition twiceLeftOverNum := 2*leftOverNum.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Definition mul2 n (v: Bit n @# ty) := (v << ($1: Bit 1 @# ty)).
    Local Definition div2 n (v: Bit n @# ty) := (v >> ($1: Bit 1 @# ty)). 
    Local Definition mod2 n (v: Bit n @# ty) := (v .& $1).

    Local Definition getPathFromIndex (i: Index @# ty) := match leftOverNum with
                                                          | 0 => i
                                                          | _ => (IF i < $twiceLeftOverNum
                                                                  then i
                                                                  else mul2 (i - $leftOverNum))
                                                          end.

    Local Definition getIndexFromPath (p: Path @# ty) := match leftOverNum with
                                                         | 0 => p
                                                         | _ => (IF p < $twiceLeftOverNum
                                                                 then p
                                                                 else div2 p + $leftOverNum)
                                                         end.

    Section state.
      Variable state: State @# ty.
      Local Fixpoint getVictimAux (depth: nat) (i: TreeIndex @# ty) (p: Path @# ty): Path ## ty :=
        match depth with
        | 0 => RetE p
        | S m => (IfE i >= $(num-1)
                  then RetE (mul2 p)
                  else (LETC direction : Bool <- state@[i];
                          LETC newIndex : TreeIndex <- mul2 i + IF #direction then $2 else $1;
                          LETC newPath : Path <- mul2 p .| IF #direction then $1 else $0;
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
      Local Fixpoint accessAux (depth: nat) (i: TreeIndex @# ty) (s: State @# ty): State ## ty :=
        match depth with
        | 0 => RetE s
        | S m => (IfE i >= $(num-1)
                  then RetE s
                  else (LETC direction: Bool <- (* pathToArray@[$$ (natToWord (Nat.log2_up PathWidth) m)] *) ((path >> ($m: Bit PathWidth @# ty)) .& $1) == $1;
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
    :  @ReplacementPolicy policyParams
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

  Transparent wlt_dec.
  Open Scope kami_expr.

  Local Notation L := (Const type false).
  Local Notation R := (Const type true).

  Definition testGetVictim (num : nat)
    := let params
         :  PolicyParams
         := {|
              StdLibKami.ReplacementPolicy.Ifc.name := "test";
              StdLibKami.ReplacementPolicy.Ifc.num  := num;
            |} in
       fun (state: State @# type) (expected : word IndexWidth) =>
         (evalLetExpr (LETE path : Path <- getVictimAux state Depth $0 $0;
                         RetE (getIndexFromPath (Var _ (SyntaxKind _) path))) = expected).
  Open Scope word.
  Goal testGetVictim (num := 3) (ARRAY {R; R}) $2. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 3) (ARRAY {R; L}) $2. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 3) (ARRAY {L; R}) $1. Proof. reflexivity. Qed.

  Goal testGetVictim (num := 6) (ARRAY {R; R; R; R; R}) $5. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {L; R; R; R; R}) $3. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {L; R; L; R; R}) $3. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {R; L; R; R; L}) $5. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {R; L; R; R; R}) $5. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 6) (ARRAY {R; R; R; L; R}) $5. Proof. reflexivity. Qed.
  
  Goal testGetVictim (num := 7) (ARRAY {R; R; R; R; R; R}) $6. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {R; R; R; L; R; R}) $6. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {R; L; L; R; R; R}) $5. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {R; L; R; R; L; R}) $6. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {L; R; R; R; R; R}) $3. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {L; R; R; R; R; L}) $3. Proof. reflexivity. Qed.
  Goal testGetVictim (num := 7) (ARRAY {L; R; L; R; R; R}) $3. Proof. reflexivity. Qed.
  Close Scope word.
  Definition evalArray
    (k : Kind)
    (n : nat)
    (arr: Array n k ## type)
    :  list (type k)
    := map (evalLetExpr arr) (getFins n).

  Definition testAccess (num : nat) :=
    let params
      :  PolicyParams
      := {|
           StdLibKami.ReplacementPolicy.Ifc.name := "test";
           StdLibKami.ReplacementPolicy.Ifc.num  := num;
         |} in
    fun (state: State @# type) (index: Index @# type) (expected : list bool) =>
      evalArray (accessAux (getPathFromIndex index) Depth $0 state) = expected.

  Goal testAccess (num := 2) (ARRAY {R}) (Const type (1'b"0")) [true]. Proof. reflexivity. Qed.
  Goal testAccess (num := 2) (ARRAY {R}) (Const type (1'b"1")) [false]. Proof. reflexivity. Qed.
  
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"01")) [true; false]. Proof. reflexivity. Qed.
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"00")) [true; true]. Proof. reflexivity. Qed.
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"10")) [false; true]. Proof. reflexivity. Qed.
  Goal testAccess (num := 3) (ARRAY {R; R}) (Const type (2'b"11")) [true; true]. Proof. reflexivity. Qed.

  Close Scope kami_expr.
  Opaque wlt_dec.
End tests.
