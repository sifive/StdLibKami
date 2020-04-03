Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.

Section DoubleFifo.
  
  Context {ifcParams : Ifc.Params}.
  Local Definition ifcParamsL :=
    Ifc.Build_Params (append name "L") k ((@size ifcParams)/2).
  Local Definition ifcParamsR :=
    Ifc.Build_Params (append name "R") k ((@size ifcParams)/2).

  Class Params := { sizePow2 : Nat.pow 2 (Nat.log2_up size) = size;
                    sizeGt1 : 1 < size;
                    fifoL : @Fifo.Ifc.Ifc ifcParamsL;
                    fifoR : @Fifo.Ifc.Ifc ifcParamsR }.

  Context {params: Params}.

  Local Lemma lgSize_double :
    ((@lgSize ifcParamsL) + 1)%nat = @lgSize ifcParams.
  Proof.
    unfold Ifc.lgSize, Ifc.size.
    cbn [ifcParamsL].
    rewrite Nat.add_comm.
    rewrite <- Nat.log2_up_mul_pow2; try lia.
    - f_equal.
      rewrite Nat.pow_1_r.
      assert (Ifc.size mod 2 = 0) as P.
      + rewrite Nat.mod_divide; [|lia].
        unfold Nat.divide.
        specialize sizePow2 as P.
        specialize sizeGt1 as P0.
        rewrite <- P.
        destruct (Nat.log2_up Ifc.size).
        * exfalso; rewrite <- P in P0; simpl in P0; lia.
        * cbn [Nat.pow].
          exists (2^n).
          apply Nat.mul_comm.
      + rewrite Nat.mul_comm.
        rewrite mul_div_exact; auto; try lia.
    - specialize sizePow2 as P.
      specialize sizeGt1 as P0.
      destruct (Nat.log2_up size).
      + exfalso; rewrite <- P in P0; simpl in P0; lia.
      + rewrite <- P; cbn[Nat.pow].
        rewrite mul_div_undo; try lia.
        specialize (Nat.pow_nonzero 2 n ltac:(lia)) as P1.
        lia.
  Qed.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition isEmpty ty: ActionT ty Bool := isEmpty fifoL.

  Local Definition isFull ty: ActionT ty Bool := isFull fifoR.
  
  Local Definition numFree ty: ActionT ty (Bit (@lgSize ifcParams)) :=
    LETA numL: Bit (@lgSize ifcParamsL) <- (Ifc.numFree fifoL);
    LETA numR: Bit (@lgSize ifcParamsR) <- (Ifc.numFree fifoR);
    Ret (castBits lgSize_double ((ZeroExtend 1 #numL) + (ZeroExtend 1 #numR))).

  Local Definition first ty: ActionT ty (Maybe k) := first fifoR.

  Local Definition deq ty: ActionT ty (Maybe k) := deq fifoR.

  Local Definition enq ty (new: ty k): ActionT ty Bool := enq fifoL new.

  Local Definition fillRule ty : ActionT ty Void :=
    LETA fullR: Bool <- (Ifc.isFull fifoR);
    LETA emptyL: Bool <- (Ifc.isEmpty fifoL);
    If !(#fullR && #emptyL) then (
      LETA val: Maybe k <- (Ifc.deq fifoL);
      LET data <- #val @% "data";
      LETA _ : Bool <- (Ifc.enq fifoR data);
      Retv
      );
    Retv.
                    
   Local Definition flush ty: ActionT ty Void :=
     LETA _ <- (Ifc.flush fifoR);
     LETA _ <- (Ifc.flush fifoL);
     Retv.

   Local Definition regs: list RegInitT := (Ifc.regs fifoL) ++ (Ifc.regs fifoR).

  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := (Ifc.regFiles fifoL) ++ (Ifc.regFiles fifoR);
      Ifc.isEmpty := isEmpty;
      Ifc.isFull := isFull;
      Ifc.numFree := numFree;
      Ifc.first := first;
      Ifc.deq := deq;
      Ifc.enq := enq;
      Ifc.flush := flush
    |}.

End DoubleFifo.
