Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Async.
Require Import StdLibKami.FreeList.Ifc.
Section AsyncTagFreeList.
  Variable name: string.

  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  Class AsyncTagFreeListParams := {
                                TagSize: nat;
                                InitName: string;
                                BackingFifo: forall {ty}, @Fifo ty (Bit TagSize);
                              }.

  Section withParams.
    Variable ty: Kind -> Type.
    Variable asyncTagFreeListParams: AsyncTagFreeListParams.
    Definition len := Nat.pow 2 TagSize. (* length of the freelist *)
    Definition Tag := Bit TagSize.

    Definition log2_up_pow_2 a := Nat.log2_up_pow2 _ (@le_0_n a).

    Definition castTag (a: ActionT ty (Maybe Tag)) :=
      match eq_sym (log2_up_pow_2 TagSize) in _ = Y return ActionT ty (Maybe (Bit Y))with
      | eq_refl => a
      end.

    Definition castTagExpr e :=
      match log2_up_pow_2 TagSize in _ = Y return Bit Y @# ty with
      | eq_refl => e
      end.
    
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition InitDone: ActionT ty (Maybe Tag) := (
      Read init: Bit TagSize <- @^InitName;
      LET initDone: Bool <- (IF (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) == $1 (* if the counter has reached len, stop *)
                             then $$true
                             else $$false);
      Ret (STRUCT { "valid" ::= #initDone;
                    "data" ::= #init }: Maybe Tag @# ty)).
    
    (* Initialization rule, which will fill the free list *)
    Definition initialize: ActionT ty Void := (
      LETA initDone: Maybe Tag <- InitDone;
      If (!(#initDone @% "valid")) then (
        LETA _ <- (Ifc.enq BackingFifo) (#initDone @% "data");
        Write @^InitName: Bit TagSize <- (#initDone @% "data") + $1;
        Retv
        );
      Retv).

  Definition nextToAlloc: ActionT ty (Maybe Tag) := (
    LETA initDone: Maybe Tag <- InitDone;
    LETA first: Maybe Tag <- (Ifc.first BackingFifo);
    LET res: Maybe Tag <- STRUCT { "valid" ::= ((#initDone @% "valid") && (#first @% "valid")) ;
                                   "data" ::= #first @% "data" };
    Ret #res).
  
  Definition alloc: ActionT ty (Maybe Tag) := (
    LETA initDone: Maybe Tag <- InitDone;
    LETA first: Maybe Tag <- (Ifc.first BackingFifo);
    LET doDequeue: Bool <- (#initDone @% "valid") && #first @% "valid";
    LET res: Maybe Tag <- STRUCT { "valid" ::= #doDequeue;
                                 "data" ::= #first @% "data" };
    If #doDequeue then (
      LETA _: Maybe Tag <- (Ifc.deq BackingFifo);
      Retv
    );
    Ret #res).
  
  Definition free (tag: Tag @# ty): ActionT ty Void := (
    LETA initDone: Maybe Tag <- InitDone;
    If (#initDone @% "valid") then (
      LETA _ <- (Ifc.enq BackingFifo) tag;
      Retv
    );
    Retv).

  Definition asyncFreeList: FreeList := Build_FreeList len initialize (castTag nextToAlloc)
                                                       (castTag alloc) (fun tag => free (castTagExpr tag)).
  End withParams.
End AsyncTagFreeList.
