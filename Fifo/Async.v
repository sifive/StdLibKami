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
      WriteName: string
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
      LETA dat: Maybe K <- first ty;
        Read deq: Bit (FifoSize + 1) <- DeqPtr;
        Write DeqPtr: Bit (FifoSize + 1) <- #deq + (IF #dat @% "valid" then $1 else $0);
        Ret #dat.

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

      Open Scope kami_scope.
      Open Scope kami_expr_scope.
      Definition regs: list RegInitT := makeModule_regs ( Register DeqPtr: Bit (FifoSize + 1) <- Default ++
                                                          Register EnqPtr: Bit (FifoSize + 1) <- Default ).
      
      Definition asyncFifo: @Fifo K :=
        {|
          Fifo.Ifc.regs := regs;
          Fifo.Ifc.isEmpty := isEmpty;
          Fifo.Ifc.isFull := isFull;
          Fifo.Ifc.first := first;
          Fifo.Ifc.deq := deq;
          Fifo.Ifc.enq := enq;
          Fifo.Ifc.flush := flush
        |}.
  End withParams.
End AsyncFifo.
  
