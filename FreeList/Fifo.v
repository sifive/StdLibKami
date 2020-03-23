Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section Impl.
  Context {ifcParams : Ifc.Params}.
  
  Context (fifo: @Fifo.Ifc.Ifc {| Fifo.Ifc.name := (name ++ ".fifo")%string;
                                  Fifo.Ifc.k    := Bit lgSize;
                                  Fifo.Ifc.size := size;
                               |}).
  
  Local Definition Tag := Bit lgSize.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition initName := (name ++ ".initTag")%string.

  Local Definition initNotDone ty: ActionT ty (Maybe Tag) := (
    Read init: Tag <- initName;
    LET initNotDone: Bool <- #init != $size;
    Ret (STRUCT { "valid" ::= #initNotDone;
                  "data" ::= #init }: Maybe Tag @# ty)).
  
  (* Initialization rule, which will fill the free list *)
  Local Definition initialize ty: ActionT ty Void := (
    LETA initNotDone: Maybe Tag <- initNotDone _;
    LET initNotDoneData <- #initNotDone @% "data";
    If ((#initNotDone @% "valid")) then (
        LETA _ <- (@Ifc.enq _ fifo ty) initNotDoneData;
        Write initName: Tag <- #initNotDoneData + $1;
        Retv
      );
    Retv).

  Local Definition nextToAlloc ty: ActionT ty (Maybe Tag) := (
    LETA initNotDone: Maybe Tag <- initNotDone _;
    LETA first: Maybe Tag <- (@Ifc.first _ fifo ty);
    LET res: Maybe Tag <- STRUCT { "valid" ::= (!(#initNotDone @% "valid") && (#first @% "valid")) ;
                                   "data" ::= #first @% "data" };
    Ret #res).

  Local Definition alloc ty (tag: ty Tag): ActionT ty Bool := (
    LETA initNotDone: Maybe Tag <- initNotDone _;
    LETA first: Maybe Tag <- (@Ifc.first _ fifo ty);
    LET doDequeue: Bool <- !(#initNotDone @% "valid") && #first @% "valid" && (#tag == #first @% "data");
    If #doDequeue then (
        LETA _: Maybe Tag <- (@Ifc.deq _ fifo ty);
        Retv
      );
    Ret #doDequeue).

  Local Definition free ty (tag: ty Tag): ActionT ty Void := (
    LETA initNotDone: Maybe Tag <- initNotDone _;
    If !(#initNotDone @% "valid") then (
        LETA _ <- (@Ifc.enq _ fifo ty) tag;
        Retv
    );
    Retv).
  
  Local Definition regs: list RegInitT := makeModule_regs ( Register initName: Tag <- $ 0 )%kami ++ (@Fifo.Ifc.regs _ fifo).
  
  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := Fifo.Ifc.regFiles fifo;
      Ifc.initialize := initialize;
      Ifc.nextToAlloc := nextToAlloc;
      Ifc.alloc := alloc;
      Ifc.free := free
    |}.
End Impl.
