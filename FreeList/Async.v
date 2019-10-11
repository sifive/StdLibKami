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

    Local Open Scope kami_expr.
    Local Open Scope kami_action.
  
  (* Initialization rule, which will fill the free list *)
  Definition initialize: ActionT ty Void :=
    Read init: Bit TagSize <- @^InitName;
    LET initDone: Bool <- (IF (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) == $1 (* if the counter has reached len, stop *)
                          then $$true
                          else $$false);
    If !#initDone then (
      (* TODO: hide enq to outside of Async? *)
      LETA suc: Bool <- (Ifc.enq BackingFifo) #init;
      If #suc then (
         Write @^InitName: Bit TagSize <- #init + $1;
         Retv
      );
      Retv
    );
    Retv.

  Definition alloc: ActionT ty (Maybe Tag) :=
    Read init: Bit TagSize <- @^InitName;
    LET initDone: Bool <- (IF (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) == $1 (* if the counter has reached len, stop *)
                          then $$true
                          else $$false);
    LETA first: Maybe Tag <- (Ifc.first BackingFifo);
    LET doDequeue: Bool <- #initDone && #first @% "valid";
    LET res: Maybe Tag <- STRUCT { "valid" ::= #doDequeue;
                                 "data" ::= #first @% "data" };
    If #doDequeue then (
      LETA _: Maybe Tag <- (Ifc.deq BackingFifo);
      Retv
    );
    Ret #res.
  
  Definition free (tag: Tag @# ty): ActionT ty Bool :=
    Read init: Bit TagSize <- @^InitName;
    LET initDone: Bool <- (IF (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) == $1 (* if the counter has reached len, stop *)
                          then $$true
                          else $$false);
    If #initDone then (
      LETA suc: Bool <- (Ifc.enq BackingFifo) tag;
      Ret #suc
    ) else (
      Ret $$false
    ) as ret;
    Ret #ret.

  Definition asyncFreeList: FreeList := Build_FreeList initialize alloc free.
  End withParams.
End AsyncTagFreeList.
