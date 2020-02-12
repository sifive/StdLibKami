Require Import Kami.AllNotations.
Require Import Kami.Utila.
Require Import StdLibKami.Fifo.Ifc.

Local Open Scope kami_expr.
Local Open Scope kami_action.

Local Close Scope kami_action.
Local Close Scope kami_expr.

Section RegListFifo.
  Context {fifoParams : FifoParams}.

  Local Definition fifoEnqRegName  := (name ++ ".enq")%string.
  Local Definition fifoDeqRegName  := (name ++ ".deq")%string.
  Local Definition fifoRegsName    := (name ++ ".regs")%string.
  Class RegListFifoParams :=
    {
      fifoLogSz: nat;
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

    Local Definition allRegs := map (fun i => (fifoRegsName ++ "_" ++ natToHexStr i)%string) (seq 0 len).

    Local Definition fastModLen ty (w : Bit (fifoLogSz + 1) @# ty): Bit fifoLogSz @# ty :=
      UniBit (TruncLsb fifoLogSz 1) w.

    Definition isEmpty ty: ActionT ty Bool :=
(*
      System [
        DispString _ "[Fifo.RegList.isEmpty]\n"
      ];
*)
      Read deq: Bit (fifoLogSz + 1) <- fifoDeqRegName;
      Read enq: Bit (fifoLogSz + 1) <- fifoEnqRegName;
      Ret (#deq == #enq).
  
    Definition isFull ty: ActionT ty Bool :=
(*
      System [
        DispString _ "[Fifo.RegList.isFull]\n"
      ];
*)
      Read deq: Bit (fifoLogSz + 1) <- fifoDeqRegName;
      Read enq: Bit (fifoLogSz + 1) <- fifoEnqRegName;
      Ret ((#deq + $len) == #enq).
    
    Definition first ty: ActionT ty (Maybe k) := 
(*
      System [
        DispString _ "[Fifo.RegList.first]\n"
      ];
*)
      LETA empty: Bool <- isEmpty ty;
      Read deq: Bit (fifoLogSz + 1) <- fifoDeqRegName;
      LET idx: Bit fifoLogSz <- (fastModLen #deq);
      LETA dat: k <- readReg allRegs len (nat_cast (fun x => Bit x @# ty) log_len_fifoLogSz #idx) _;
      Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe k @# ty).

    Definition deq ty: ActionT ty (Maybe k) :=
(*
      System [
        DispString _ "[Fifo.RegList.deq]\n"
      ];
*)
      LETA data: Maybe k <- first ty;
      Read deq: Bit (fifoLogSz + 1) <- fifoDeqRegName;
      Write fifoDeqRegName: Bit (fifoLogSz + 1) <- #deq + (IF #data @% "valid" then $1 else $0);
      Ret #data.

    Definition enq ty (new: ty k): ActionT ty Bool :=
(*
      System [
        DispString _ "[Fifo.RegList.enq]\n";
        DispString _ ("[Fifo.RegList.enq] fifo size: " ++ nat_decimal_string fifoLogSz ++ "\n")
      ];
*)
      Read enq: Bit (fifoLogSz + 1) <- fifoEnqRegName;
(*
      System [
        DispString _ ("[Fifo.RegList.enq] enq from " ++ fifoEnqRegName ++ ": ");
        DispHex #enq;
        DispString _ "\n"
      ];
*)
      LET idx: Bit fifoLogSz <- (fastModLen #enq);
(*
      System [
        DispString _ "[Fifo.RegList.enq] idx: ";
        DispHex #idx;
        DispString _ "\n"
      ];
*)
      LETA full: Bool <- isFull ty;
      If !#full then (
(*
        System [
          DispString _ "[Fifo.RegList.enq] writing to idx.\n"
        ];
*)
        Write fifoEnqRegName: Bit (fifoLogSz + 1) <- #enq + $1;
        writeReg allRegs len (nat_cast (fun x => Bit x @# ty) log_len_fifoLogSz #idx) #new
        );
      Ret !#full.
      
      Definition flush ty: ActionT ty Void :=
(*
        System [
          DispString _ "[Fifo.RegList.flush]\n"
        ];
*)
        Write fifoDeqRegName: Bit (fifoLogSz + 1) <- $0;
        Write fifoEnqRegName: Bit (fifoLogSz + 1) <- $0;
        Retv.

      Definition regs: list RegInitT := makeModule_regs ( Register fifoDeqRegName: Bit (fifoLogSz + 1) <- Default ++
                                                          Register fifoEnqRegName: Bit (fifoLogSz + 1) <- Default ++
                                                          map (fun i => MERegister (fifoRegsName ++ "_" ++ natToHexStr i, existT RegInitValT (SyntaxKind k) None)%string)
                                                              (seq 0 len))%kami.

      Instance regListFifo: @Fifo fifoParams :=
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
