Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.

Local Open Scope kami_expr.
Local Open Scope kami_action.

Definition readReg ty (ls: list string) len (idx: Bit (Nat.log2_up len) @# ty) k :=
  GatherActions (map (fun '(i, reg) => Read val: k <- reg;
                                       Ret (IF $i == idx then pack #val else $0)) (tag ls)) as vals;
    Ret (unpack k (CABit Bor vals)).
    
Definition writeReg ty (ls: list string) len (idx: Bit (Nat.log2_up len) @# ty) k (newval: k @# ty) :=
  GatherActions (map (fun '(i, reg) => Read val: k <- reg;
                                       Write reg: k <- (IF $i == idx then newval else #val);
                                       Retv) (tag ls)) as _;
    Retv.
    
Local Close Scope kami_action.
Local Close Scope kami_expr.

Section RegListFifo.
  Class RegListFifoParams :=
    {
      k: Kind;
      fifoLogSz: nat;
      enqPtr: string;
      deqPtr: string;
      regsName: string;
    }.

  Section withParams.
    Context {regListFifoParams: RegListFifoParams}.
    Local Definition len := Nat.pow 2 fifoLogSz.
    Local Definition twoLen := 2 * len.

    Lemma log_len_fifoLogSz: fifoLogSz = Nat.log2_up len.
    Proof.
      unfold len.
      rewrite Nat.log2_up_pow2; try Omega.omega.
    Qed.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Definition allRegs := map (fun i => (regsName ++ "_" ++ natToHexStr i)%string) (seq 0 len).

    Local Definition fastModLen ty (w : Bit (fifoLogSz + 1) @# ty): Bit fifoLogSz @# ty :=
      UniBit (TruncLsb fifoLogSz 1) w.

    Definition isEmpty ty: ActionT ty Bool :=
      System [
        DispString _ "[Fifo.RegList.isEmpty]\n"
      ];
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      Read enq: Bit (fifoLogSz + 1) <- enqPtr;
      Ret (#deq == #enq).
  
    Definition isFull ty: ActionT ty Bool :=
      System [
        DispString _ "[Fifo.RegList.isFull]\n"
      ];
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      Read enq: Bit (fifoLogSz + 1) <- enqPtr;
      Ret ((#deq + $len) == #enq).
    
    Definition first ty: ActionT ty (Maybe k) := 
      System [
        DispString _ "[Fifo.RegList.first]\n"
      ];
      LETA empty: Bool <- isEmpty ty;
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      LET idx: Bit fifoLogSz <- (fastModLen #deq);
      LETA dat: k <- readReg allRegs len (nat_cast (fun x => Bit x @# ty) log_len_fifoLogSz #idx) _;
      Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe k @# ty).

    Definition deq ty: ActionT ty (Maybe k) :=
      System [
        DispString _ "[Fifo.RegList.deq]\n"
      ];
      LETA data: Maybe k <- first ty;
      Read deq: Bit (fifoLogSz + 1) <- deqPtr;
      Write deqPtr: Bit (fifoLogSz + 1) <- #deq + (IF #data @% "valid" then $1 else $0);
      Ret #data.

    Definition enq ty (new: ty k): ActionT ty Bool :=
      System [
        DispString _ "[Fifo.RegList.enq]\n";
        DispString _ ("[Fifo.RegList.enq] fifo size: " ++ nat_decimal_string fifoLogSz ++ "\n")
      ];
      Read enq: Bit (fifoLogSz + 1) <- enqPtr;
      System [
        DispString _ ("[Fifo.RegList.enq] enq from " ++ enqPtr ++ ": ");
        DispHex #enq;
        DispString _ "\n"
      ];
      LET idx: Bit fifoLogSz <- (fastModLen #enq);
      System [
        DispString _ "[Fifo.RegList.enq] idx: ";
        DispHex #idx;
        DispString _ "\n"
      ];
      LETA full: Bool <- isFull ty;
      If !#full then (
        System [
          DispString _ "[Fifo.RegList.enq] writing to idx.\n"
        ];
        Write enqPtr: Bit (fifoLogSz + 1) <- #enq + $1;
        writeReg allRegs len (nat_cast (fun x => Bit x @# ty) log_len_fifoLogSz #idx) #new
        );
      Ret !#full.
      
      Definition flush ty: ActionT ty Void :=
        System [
          DispString _ "[Fifo.RegList.flush]\n"
        ];
        Write deqPtr: Bit (fifoLogSz + 1) <- $0;
        Write enqPtr: Bit (fifoLogSz + 1) <- $0;
        Retv.

      Definition regs: list RegInitT := makeModule_regs ( Register deqPtr: Bit (fifoLogSz + 1) <- Default ++
                                                          Register enqPtr: Bit (fifoLogSz + 1) <- Default ++
                                                          map (fun i => MERegister (regsName ++ "_" ++ natToHexStr i, existT RegInitValT (SyntaxKind k) None)%string)
                                                              (seq 0 len))%kami.

      Instance regListFifo: @Fifo k :=
        {|
          Fifo.Ifc.getLen := len;
          Fifo.Ifc.regs := regs;
          Fifo.Ifc.regFiles := [];
          Fifo.Ifc.isEmpty := isEmpty;
          Fifo.Ifc.isFull := isFull;
          Fifo.Ifc.first := first;
          Fifo.Ifc.deq := deq;
          Fifo.Ifc.enq := enq;
          Fifo.Ifc.flush := flush
        |}.
  End withParams.
End RegListFifo.
