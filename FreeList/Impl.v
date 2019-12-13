Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.FreeList.Ifc.
Section ImplTagFreeList.
  Class ImplTagFreeListParams := {
                                TagSize: nat;
                                InitName: string;
                                BackingFifo: @Fifo (Bit (Nat.log2_up (Nat.pow 2 TagSize)));
                              }.

  Section withParams.
    Context (implTagFreeListParams: ImplTagFreeListParams).
    
    Definition len := Nat.pow 2 TagSize. (* length of the freelist *)
    Definition CastTagSize := Nat.log2_up len.
    Definition Tag := Bit CastTagSize.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section withTy.
      Context (ty: Kind -> Type).

      Definition InitDone: ActionT ty (Maybe Tag) := (
        Read init: Tag <- InitName;
        LET initDone: Bool <- (IF (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) == $1 (* if the counter has reached len, stop *)
                               then $$true
                               else $$false);
        Ret (STRUCT { "valid" ::= #initDone;
                      "data" ::= #init }: Maybe Tag @# ty)).
    
    (* Initialization rule, which will fill the free list *)
      Definition initialize: ActionT ty Void := (
        LETA initDone: Maybe Tag <- InitDone;
        LET initDoneDat <- #initDone @% "data";
        If (!(#initDone @% "valid")) then (
            LETA _ <- (Ifc.enq BackingFifo) initDoneDat;
            Write InitName: Tag <- (#initDone @% "data") + $1;
            Retv
          );
        Retv).

      Definition nextToAlloc: ActionT ty (Maybe Tag) := (
        LETA initDone: Maybe Tag <- InitDone;
        LETA first: Maybe Tag <- (Ifc.first BackingFifo);
        LET res: Maybe Tag <- STRUCT { "valid" ::= ((#initDone @% "valid") && (#first @% "valid")) ;
                                       "data" ::= #first @% "data" };
        Ret #res).
  
      Definition alloc (a: ty Tag): ActionT ty Bool := (
        LETA initDone: Maybe Tag <- InitDone;
        LETA first: Maybe Tag <- (Ifc.first BackingFifo);
        LET doDequeue: Bool <- (#initDone @% "valid") && #first @% "valid" && (#a == #first @% "data");
        If #doDequeue then (
            LETA _: Maybe Tag <- (Ifc.deq BackingFifo);
            Retv
          );
        Ret #doDequeue).
  
      Definition free (tag: ty Tag): ActionT ty Void := (
        LETA initDone: Maybe Tag <- InitDone;
        If (#initDone @% "valid") then (
            LETA _ <- (Ifc.enq BackingFifo) tag;
            Retv
        );
        Retv).


    End withTy.
    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    
    Definition regs: list RegInitT := makeModule_regs ( Register InitName: Tag <- $ 0 ) ++ (Fifo.Ifc.regs BackingFifo).
    
    Definition implFreeList: FreeList :=
      {|
        FreeList.Ifc.regs := regs;
        FreeList.Ifc.length := len;
        FreeList.Ifc.initialize := initialize;
        FreeList.Ifc.nextToAlloc := nextToAlloc;
        FreeList.Ifc.alloc := alloc;
        FreeList.Ifc.free := free
      |}.
  End withParams.
End ImplTagFreeList.
