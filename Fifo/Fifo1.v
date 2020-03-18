Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.Fifo.Ifc.

Section Fifo1.
  Context {ifcParams : Ifc.Params}.

  Class Params := {size1 := size = 1}.

  Context {params: Params}.

  Local Definition twoSize := 2 * size.

  Local Definition validRegName := (name ++ ".validReg")%string.
  Local Definition dataRegName := (name ++ ".dataReg")%string.
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition isEmpty ty: ActionT ty Bool :=
    Read val: Bool <- validRegName;
    Ret (!#val).

  Local Definition isFull ty: ActionT ty Bool :=
    Read val: Bool <- validRegName;
    Ret (#val).
  
  Local Definition numFree ty: ActionT ty (Bit lgSize) :=
    Read val: Bool <- validRegName;
    Ret (IF #val then $0 else $1).
  
  Local Definition first ty: ActionT ty (Maybe k) :=
    Read val: Bool <- validRegName;
    Read dat: k <- dataRegName;
    Ret (STRUCT { "valid" ::= #val; "data" ::= #dat} : Maybe k @# ty).
  
  Local Definition deq ty: ActionT ty (Maybe k) :=
    Read val: Bool <- validRegName;
    Read dat: k <- dataRegName;
    Write validRegName: Bool <- $$(false);
    Ret (STRUCT { "valid" ::= #val; "data" ::= #dat} : Maybe k @# ty).

  Local Definition enq ty (new: ty k): ActionT ty Bool :=
    Read val: Bool <- validRegName;
    Read dat: k <- dataRegName;
    Write validRegName: Bool <- $$(true);
    Write dataRegName: k <- IF !#val then #new else #dat;
    Ret !#val.

  Local Definition flush ty: ActionT ty Void :=
    Write validRegName <- $$(false);                
    Retv.

   Local Definition regs: list RegInitT :=
                    makeModule_regs (Register validRegName: Bool <- Default ++
                                     Register dataRegName: k <- Default)%kami.

  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := nil;
      Ifc.isEmpty := isEmpty;
      Ifc.isFull := isFull;
      Ifc.numFree := numFree;
      Ifc.first := first;
      Ifc.deq := deq;
      Ifc.enq := enq;
      Ifc.flush := flush
    |}.
End Fifo1.
