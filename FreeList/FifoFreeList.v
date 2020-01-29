Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.FreeList.Ifc.
Section ImplTagFreeList.
  Class ImplTagFreeListParams := {
                                len: nat;
                                initName: string;
                                backingFifo: @Fifo (Bit (Nat.log2_up len));
                              }.

  Section withParams.
    Context (implTagFreeListParams: ImplTagFreeListParams).
    
    Definition Tag := Bit (Nat.log2_up len).

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section withTy.
      Context (ty: Kind -> Type).

      Definition InitNotDone: ActionT ty (Maybe Tag) := (
        Read init: Tag <- initName;
        LET initNotDone: Bool <- (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) != $1;
        Ret (STRUCT { "valid" ::= #initNotDone;
                      "data" ::= #init }: Maybe Tag @# ty)).
    
    (* Initialization rule, which will fill the free list *)
      Definition initialize: ActionT ty Void := (
        LETA initNotDone: Maybe Tag <- InitNotDone;
        LET initNotDoneData <- #initNotDone @% "data";
        If ((#initNotDone @% "valid")) then (
            LETA _ <- (@Ifc.enq _ backingFifo ty) initNotDoneData;
            Write initName: Tag <- #initNotDoneData + $1;
            Retv
          );
        Retv).

      Definition nextToAlloc: ActionT ty (Maybe Tag) := (
        LETA initNotDone: Maybe Tag <- InitNotDone;
        LETA first: Maybe Tag <- (@Ifc.first _ backingFifo ty);
        LET res: Maybe Tag <- STRUCT { "valid" ::= (!(#initNotDone @% "valid") && (#first @% "valid")) ;
                                       "data" ::= #first @% "data" };
        Ret #res).
  
      Definition alloc (tag: ty Tag): ActionT ty Bool := (
        LETA initNotDone: Maybe Tag <- InitNotDone;
        LETA first: Maybe Tag <- (@Ifc.first _ backingFifo ty);
        LET doDequeue: Bool <- !(#initNotDone @% "valid") && #first @% "valid" && (#tag == #first @% "data");
        If #doDequeue then (
            LETA _: Maybe Tag <- (@Ifc.deq _ backingFifo ty);
            Retv
          );
        Ret #doDequeue).
  
      Definition free (tag: ty Tag): ActionT ty Void := (
        LETA initNotDone: Maybe Tag <- InitNotDone;
        If !(#initNotDone @% "valid") then (
            LETA _ <- (@Ifc.enq _ backingFifo ty) tag;
            Retv
        );
        Retv).

    End withTy.
    
    Definition regs: list RegInitT := makeModule_regs ( Register initName: Tag <- $ 0 )%kami ++ (@Fifo.Ifc.regs _ backingFifo).
    
    Instance implFreeList: FreeList :=
      {|
        FreeList.Ifc.regs := regs;
        FreeList.Ifc.regFiles := @Fifo.Ifc.regFiles _ backingFifo;
        FreeList.Ifc.length := len;
        FreeList.Ifc.initialize := initialize;
        FreeList.Ifc.nextToAlloc := nextToAlloc;
        FreeList.Ifc.alloc := alloc;
        FreeList.Ifc.free := free
      |}.
  End withParams.
End ImplTagFreeList.
