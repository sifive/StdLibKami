Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section AsyncFifo.
  Class AsyncFifoParams :=
    {
      k: Kind;
      fifoLogSz: nat;
      enqPtr: string;
      deqPtr: string;
      readName: string;
      writeName: string;
      dataName: string
    }.

  Section withParams.
    Context {asyncFifoParams: AsyncFifoParams}.
    Local Definition len := Nat.pow 2 fifoLogSz.
    Local Definition twoLen := 2 * len.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.
  
    Local Definition fastModLen ty (w : Bit (fifoLogSz + 1) @# ty): Bit fifoLogSz @# ty :=
      UniBit (TruncLsb fifoLogSz 1) w.

    Definition isEmpty ty: ActionT ty Bool :=
      System [
        DispString _ "[Fifo.Async.isEmpty]\n"
      ];
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      Read enq: Bit (fifoLogSz + 1) <- enqPtr;
      Ret (#deq == #enq).
  
    Definition isFull ty: ActionT ty Bool :=
      System [
        DispString _ "[Fifo.Async.isFull]\n"
      ];
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      Read enq: Bit (fifoLogSz + 1) <- enqPtr;
      Ret ((#deq + $len) == #enq).
    
    Definition first ty: ActionT ty (Maybe k) := 
      System [
        DispString _ "[Fifo.Async.first]\n"
      ];
      LETA empty: Bool <- isEmpty ty;
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      LET idx: Bit fifoLogSz <- (fastModLen #deq);
      ReadRf dat: k <- readName(#idx: Bit fifoLogSz);
      Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe k @# ty).

    Definition deq ty: ActionT ty (Maybe k) :=
      System [
        DispString _ "[Fifo.Async.deq]\n"
      ];
      LETA data: Maybe k <- first ty;
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      Write deqPtr: Bit (fifoLogSz + 1) <- #deq + (IF #data @% "valid" then $1 else $0);
      Ret #data.

    Definition enq ty (new: ty k): ActionT ty Bool :=
      System [
        DispString _ "[Fifo.Async.enq]\n";
        DispString _ ("[Fifo.Async.enq] fifo size: " ++ nat_decimal_string fifoLogSz ++ "\n")
      ];
      Read enq: Bit (fifoLogSz + 1) <- enqPtr;
      System [
        DispString _ ("[Fifo.Async.enq] enq from " ++ enqPtr ++ ": ");
        DispHex #enq;
        DispString _ "\n"
      ];
      LET idx: Bit fifoLogSz <- (fastModLen #enq);
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
        WriteRf writeName(#idx : fifoLogSz ; #new : k);
        Write enqPtr: Bit (fifoLogSz + 1) <- #enq + $1;
        Retv
        );
      Ret !#full.
      
      Definition flush ty: ActionT ty Void :=
        System [
          DispString _ "[Fifo.Async.flush]\n"
        ];
        Write deqPtr: Bit (fifoLogSz + 1) <- $0;
        Write enqPtr: Bit (fifoLogSz + 1) <- $0;
        Retv.

      Definition regs: list RegInitT := makeModule_regs ( Register deqPtr: Bit (fifoLogSz + 1) <- Default ++
                                                          Register enqPtr: Bit (fifoLogSz + 1) <- Default )%kami.

      Definition regFiles: list RegFileBase
        := [
             @Build_RegFileBase false 1 dataName
               (Async [readName]) writeName len k (@RFNonFile _ _ None)
           ].

      Instance asyncFifo: @Fifo k :=
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
