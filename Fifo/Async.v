Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section AsyncFifo.
  Class AsyncFifoParams :=
    {
      K: Kind;
      FifoSize: nat;
      EnqPtr: string;
      DeqPtr: string;
      ReadName: string;
      WriteName: string;
      DataName: string
    }.

  Section withParams.
    Context {asyncFifoParams: AsyncFifoParams}.
    Local Definition len := Nat.pow 2 FifoSize.
    Local Definition twoLen := 2 * len.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.
  
    Local Definition fastModLen ty (w : Bit (FifoSize + 1) @# ty): Bit FifoSize @# ty :=
      UniBit (TruncLsb FifoSize 1) w.

    Definition isEmpty ty: ActionT ty Bool :=
      Read deq: Bit (FifoSize + 1) <- DeqPtr;
      Read enq: Bit (FifoSize + 1) <- EnqPtr;
      Ret (#deq == #enq).
  
    Definition isFull ty: ActionT ty Bool :=
      Read deq: Bit (FifoSize + 1) <- DeqPtr;
      Read enq: Bit (FifoSize + 1) <- EnqPtr;
      Ret ((#deq + $len) == #enq).
    
    Definition first ty: ActionT ty (Maybe K) := 
      LETA empty: Bool <- isEmpty ty;
      Read deq: Bit (FifoSize + 1) <- DeqPtr;
      LET idx: Bit FifoSize <- (fastModLen #deq);
      Call dat: K <- ReadName(#idx: Bit FifoSize);
      Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe K @# ty).

    Definition deq ty: ActionT ty (Maybe K) :=
      LETA data: Maybe K <- first ty;
      Read deq: Bit (FifoSize + 1) <- DeqPtr;
      Write DeqPtr: Bit (FifoSize + 1) <- #deq + (IF #data @% "valid" then $1 else $0);
      Ret #data.

    Definition enq ty (new: ty K): ActionT ty Bool :=
      Read enq: Bit (FifoSize + 1) <- EnqPtr;
      LET idx: Bit FifoSize <- (fastModLen #enq);
      LETA full: Bool <- isFull ty;
      If !#full then (
        Call WriteName(STRUCT { "addr" ::= #idx;
                                "data" ::= #new } : WriteRq FifoSize K );
        Write EnqPtr: Bit (FifoSize + 1) <- #enq + $1;
        Retv
        );
      Ret !#full.
      
      Definition flush ty: ActionT ty Void :=
        Write DeqPtr: Bit (FifoSize + 1) <- $0;
        Write EnqPtr: Bit (FifoSize + 1) <- $0;
        Retv.

      Definition regs: list RegInitT := makeModule_regs ( Register DeqPtr: Bit (FifoSize + 1) <- Default ++
                                                          Register EnqPtr: Bit (FifoSize + 1) <- Default )%kami.

      Definition regFiles: list RegFileBase
        := [
             @Build_RegFileBase false 1 DataName
               (Async [ReadName]) WriteName FifoSize K (@RFNonFile _ _ None)
           ].

      Instance asyncFifo: @Fifo K :=
        {|
          Fifo.Ifc.getLen := len;
          Fifo.Ifc.regs := regs;
          Fifo.Ifc.regFiles := regFiles;
          Fifo.Ifc.isEmpty := isEmpty;
          Fifo.Ifc.isFull := isFull;
          Fifo.Ifc.first := first;
          Fifo.Ifc.deq := deq;
          Fifo.Ifc.enq := enq;
          Fifo.Ifc.flush := flush
        |}.
  End withParams.
End AsyncFifo.
