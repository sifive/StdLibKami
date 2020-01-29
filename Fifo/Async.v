Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section AsyncFifo.
  Class AsyncFifoParams :=
    {
      K: Kind;
      FifoLogSz: nat;
      EnqPtr: string;
      DeqPtr: string;
      ReadName: string;
      WriteName: string;
      DataName: string
    }.

  Section withParams.
    Context {asyncFifoParams: AsyncFifoParams}.
    Local Definition len := Nat.pow 2 FifoLogSz.
    Local Definition twoLen := 2 * len.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.
  
    Local Definition fastModLen ty (w : Bit (FifoLogSz + 1) @# ty): Bit FifoLogSz @# ty :=
      UniBit (TruncLsb FifoLogSz 1) w.

    Definition isEmpty ty: ActionT ty Bool :=
      System [
        DispString _ "[Fifo.Async.isEmpty]\n"
      ];
      Read deq: Bit (FifoLogSz + 1) <- DeqPtr;
      Read enq: Bit (FifoLogSz + 1) <- EnqPtr;
      Ret (#deq == #enq).
  
    Definition isFull ty: ActionT ty Bool :=
      System [
        DispString _ "[Fifo.Async.isFull]\n"
      ];
      Read deq: Bit (FifoLogSz + 1) <- DeqPtr;
      Read enq: Bit (FifoLogSz + 1) <- EnqPtr;
      Ret ((#deq + $len) == #enq).
    
    Definition first ty: ActionT ty (Maybe K) := 
      System [
        DispString _ "[Fifo.Async.first]\n"
      ];
      LETA empty: Bool <- isEmpty ty;
      Read deq: Bit (FifoLogSz + 1) <- DeqPtr;
      LET idx: Bit FifoLogSz <- (fastModLen #deq);
      ReadRf dat: K <- ReadName(#idx: Bit FifoLogSz);
      Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe K @# ty).

    Definition deq ty: ActionT ty (Maybe K) :=
      System [
        DispString _ "[Fifo.Async.deq]\n"
      ];
      LETA data: Maybe K <- first ty;
      Read deq: Bit (FifoLogSz + 1) <- DeqPtr;
      Write DeqPtr: Bit (FifoLogSz + 1) <- #deq + (IF #data @% "valid" then $1 else $0);
      Ret #data.

    Definition enq ty (new: ty K): ActionT ty Bool :=
      System [
        DispString _ "[Fifo.Async.enq]\n";
        DispString _ ("[Fifo.Async.enq] fifo size: " ++ nat_decimal_string FifoLogSz ++ "\n")
      ];
      Read enq: Bit (FifoLogSz + 1) <- EnqPtr;
      System [
        DispString _ ("[Fifo.Async.enq] enq from " ++ EnqPtr ++ ": ");
        DispHex #enq;
        DispString _ "\n"
      ];
      LET idx: Bit FifoLogSz <- (fastModLen #enq);
      System [
        DispString _ "[Fifo.Async.enq] idx: ";
        DispHex #idx;
        DispString _ "\n"
      ];
      LETA full: Bool <- isFull ty;
      If !#full then (
        System [
          DispString _ "[Fifo.Async.enq] writing to idx.\n"
        ];
        WriteRf WriteName(#idx : FifoLogSz ; #new : K);
        Write EnqPtr: Bit (FifoLogSz + 1) <- #enq + $1;
        Retv
        );
      Ret !#full.
      
      Definition flush ty: ActionT ty Void :=
        System [
          DispString _ "[Fifo.Async.flush]\n"
        ];
        Write DeqPtr: Bit (FifoLogSz + 1) <- $0;
        Write EnqPtr: Bit (FifoLogSz + 1) <- $0;
        Retv.

      Definition regs: list RegInitT := makeModule_regs ( Register DeqPtr: Bit (FifoLogSz + 1) <- Default ++
                                                          Register EnqPtr: Bit (FifoLogSz + 1) <- Default )%kami.

      Definition regFiles: list RegFileBase
        := [
             @Build_RegFileBase false 1 DataName
               (Async [ReadName]) WriteName len K (@RFNonFile _ _ None)
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
