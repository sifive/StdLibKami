Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section ImplTagFreeList.
  Context {freeListParams : FreeListParams}.

  Local Definition initName := (name ++ ".initTag")%string.

  Section withParams.
    Context (backingFifo: @Fifo ({|
                                    StdLibKami.Fifo.Ifc.name := (StdLibKami.FreeList.Ifc.name ++ ".backingFifo")%string;
                                    StdLibKami.Fifo.Ifc.k    := Bit tagSz
                                  |})).
    
    Local Definition Tag := Bit tagSz.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Definition initNotDone ty: ActionT ty (Maybe Tag) := (
      Read init: Tag <- initName;
      LET initNotDone: Bool <- (ZeroExtendTruncMsb _ #init: Bit 1 @# ty) != $1;
      Ret (STRUCT { "valid" ::= #initNotDone;
                    "data" ::= #init }: Maybe Tag @# ty)).
    
    (* Initialization rule, which will fill the free list *)
    Local Definition initialize ty: ActionT ty Void := (
      LETA initNotDone: Maybe Tag <- initNotDone _;
      LET initNotDoneData <- #initNotDone @% "data";
      If ((#initNotDone @% "valid")) then (
          LETA _ <- (@Ifc.enq _ backingFifo ty) initNotDoneData;
          Write initName: Tag <- #initNotDoneData + $1;
          Retv
        );
      Retv).

    Local Definition nextToAlloc ty: ActionT ty (Maybe Tag) := (
      LETA initNotDone: Maybe Tag <- initNotDone _;
      LETA first: Maybe Tag <- (@Ifc.first _ backingFifo ty);
      LET res: Maybe Tag <- STRUCT { "valid" ::= (!(#initNotDone @% "valid") && (#first @% "valid")) ;
                                     "data" ::= #first @% "data" };
      Ret #res).
  
    Local Definition alloc ty (tag: ty Tag): ActionT ty Bool := (
      LETA initNotDone: Maybe Tag <- initNotDone _;
      LETA first: Maybe Tag <- (@Ifc.first _ backingFifo ty);
      LET doDequeue: Bool <- !(#initNotDone @% "valid") && #first @% "valid" && (#tag == #first @% "data");
      If #doDequeue then (
          LETA _: Maybe Tag <- (@Ifc.deq _ backingFifo ty);
          Retv
        );
      Ret #doDequeue).
  
    Local Definition free ty (tag: ty Tag): ActionT ty Void := (
      LETA initNotDone: Maybe Tag <- initNotDone _;
      If !(#initNotDone @% "valid") then (
          LETA _ <- (@Ifc.enq _ backingFifo ty) tag;
          Retv
      );
      Retv).
    
    Local Definition regs: list RegInitT := makeModule_regs ( Register initName: Tag <- $ 0 )%kami ++ (@Fifo.Ifc.regs _ backingFifo).
    
    Definition fifoFreeList: FreeList :=
      {|
        FreeList.Ifc.regs := regs;
        FreeList.Ifc.regFiles := @Fifo.Ifc.regFiles _ backingFifo;
        FreeList.Ifc.length := Nat.pow 2 tagSz;
        FreeList.Ifc.initialize := initialize;
        FreeList.Ifc.nextToAlloc := nextToAlloc;
        FreeList.Ifc.alloc := alloc;
        FreeList.Ifc.free := free
      |}.
  End withParams.
End ImplTagFreeList.
