Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Impl.

Section DoubleFifo.
  
  Context {ifcParams : Ifc.Params}.
  (* Variable sizeL sizeR : nat. *)
  (* Local Definition ifcParamsL := *)
  (*   Ifc.Build_Params (append name "L") k sizeL. *)
  (* Local Definition ifcParamsR := *)
  (*   Ifc.Build_Params (append name "R") k sizeR. *)

  Class Params := { sizeL : nat;
                    sizeR : nat;
                    sizeSum : (@size ifcParams) = sizeL + sizeR;
                    Lfifo : @Fifo.Ifc.Ifc (Ifc.Build_Params (append (@name ifcParams) "L")
                                                            (@k ifcParams)
                                                            sizeL);
                    Rfifo : @Fifo.Ifc.Ifc (Ifc.Build_Params (append (@name ifcParams) "R")
                                                            (@k ifcParams)
                                                            sizeR);
                    }.
                   (* ifcParamsL : Ifc.Params; *)
                   (*  ifcParamsR : Ifc.Params; *)
                   (*  sizeSum : (@size ifcParams) = (@size ifcParamsL) + (@size ifcParamsR); *)
                   (*  sameKindL : (@k ifcParams) = (@k ifcParamsL); *)
                   (*  sameKindR : (@k ifcParams) = (@k ifcParamsR); *)
                   (*  nameL : (@name ifcParamsL) = (append (@name ifcParams) "L"); *)
                   (*  nameR : (@name ifcParamsR) = (append (@name ifcParams) "R"); *)
                   (*  sizeGt1 : 1 < size; *)
                   (*  Lfifo : @Fifo.Ifc.Ifc ifcParamsL; *)
                   (*  Rfifo : @Fifo.Ifc.Ifc ifcParamsR }. *)

  Context {params: Params}.
  
  (* Local Lemma lgSize_double : *)
  (*   ((@lgSize ifcParamsL) + 1)%nat = @lgSize ifcParams. *)
  (* Proof. *)
  (*   unfold Ifc.lgSize, Ifc.size. *)
  (*   cbn [ifcParamsL]. *)
  (*   rewrite Nat.add_comm. *)
  (*   rewrite <- Nat.log2_up_mul_pow2; try lia. *)
  (*   - f_equal. *)
  (*     rewrite Nat.pow_1_r. *)
  (*     assert (Ifc.size mod 2 = 0) as P. *)
  (*     + rewrite Nat.mod_divide; [|lia]. *)
  (*       unfold Nat.divide. *)
  (*       specialize sizePow2 as P. *)
  (*       specialize sizeGt1 as P0. *)
  (*       rewrite <- P. *)
  (*       destruct (Nat.log2_up Ifc.size). *)
  (*       * exfalso; rewrite <- P in P0; simpl in P0; lia. *)
  (*       * cbn [Nat.pow]. *)
  (*         exists (2^n). *)
  (*         apply Nat.mul_comm. *)
  (*     + rewrite Nat.mul_comm. *)
  (*       rewrite mul_div_exact; auto; try lia. *)
  (*   - specialize sizePow2 as P. *)
  (*     specialize sizeGt1 as P0. *)
  (*     destruct (Nat.log2_up size). *)
  (*     + exfalso; rewrite <- P in P0; simpl in P0; lia. *)
  (*     + rewrite <- P; cbn[Nat.pow]. *)
  (*       rewrite mul_div_undo; try lia. *)
  (*       specialize (Nat.pow_nonzero 2 n ltac:(lia)) as P1. *)
  (*       lia. *)
  (* Qed. *)

  Local Lemma lgSize_sumL :
    (@lgSize (Ifc.Build_Params (append (@name ifcParams) "L")
                               (@k ifcParams)
                               sizeL))
    + (lgSize - (@lgSize (Ifc.Build_Params (append (@name ifcParams) "L")
                                           (@k ifcParams)
                                           sizeL))) = lgSize.
  Proof.
    symmetry.
    apply le_plus_minus.
    unfold lgSize.
    apply Nat.log2_up_le_mono.
    rewrite sizeSum; unfold size; lia.
  Qed.

  Local Lemma lgSize_sumR :
    (@lgSize (Ifc.Build_Params (append (@name ifcParams) "R")
                               (@k ifcParams)
                               sizeR))
    + (lgSize - (@lgSize (Ifc.Build_Params (append (@name ifcParams) "R")
                                           (@k ifcParams)
                                           sizeR))) = lgSize.
  Proof.
    symmetry.
    apply le_plus_minus.
    unfold lgSize.
    apply Nat.log2_up_le_mono.
    rewrite sizeSum; unfold size; lia.
  Qed.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition isEmpty ty: ActionT ty Bool := isEmpty Lfifo.

  Local Definition isFull ty: ActionT ty Bool := isFull Rfifo.
  
  Local Definition numFree ty: ActionT ty (Bit (@lgSize ifcParams)) :=
    LETA numL : Bit lgSize <- (Ifc.numFree Lfifo);
    LETA numR : Bit lgSize <- (Ifc.numFree Rfifo);
    Ret (IF (#numL < $(sizeL))
         then (castBits lgSize_sumL (ZeroExtend _ #numL))
         else (castBits lgSize_sumL (ZeroExtend _ #numL)
               + castBits lgSize_sumR (ZeroExtend _ #numR))).
  
  Local Definition first ty: ActionT ty (Maybe k) := first Rfifo.

  Local Definition deq ty: ActionT ty (Maybe k) := deq Rfifo.

  Local Definition enq ty (new: ty k): ActionT ty Bool := enq Lfifo new.

  Local Definition fillRule ty : ActionT ty Void :=
    LETA fullR: Bool <- (Ifc.isFull Rfifo);
    LETA emptyL: Bool <- (Ifc.isEmpty Lfifo);
    If !(#fullR && #emptyL) then (
      LETA val: Maybe k <- (Ifc.deq Lfifo);
      LET data <- #val @% "data";
      LETA _ : Bool <- (Ifc.enq Rfifo data);
      Retv
      );
    Retv.
                    
  Local Definition flush ty: ActionT ty Void :=
    LETA _ <- (Ifc.flush Rfifo);
    LETA _ <- (Ifc.flush Lfifo);
    Retv.

  Local Definition regs: list RegInitT := (Ifc.regs Lfifo) ++ (Ifc.regs Rfifo).

  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := (Ifc.regFiles Lfifo) ++ (Ifc.regFiles Rfifo);
      Ifc.isEmpty := isEmpty;
      Ifc.isFull := isFull;
      Ifc.numFree := numFree;
      Ifc.first := first;
      Ifc.deq := deq;
      Ifc.enq := enq;
      Ifc.flush := flush
    |}.
  
End DoubleFifo.
