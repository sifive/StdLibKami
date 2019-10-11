Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Interface.
Section AsyncFifo.
  Context (size: nat).
  Local Definition len := Nat.pow 2 size.
  Local Definition twoLen := 2 * len.
  Context (k: Kind). (* content *)
  
  Context (ty: Kind -> Type).
  Context (name: string).
  Local Notation "@^ x" := (name ++ "_" ++ x)%string (at level 0).

  (* Prefix from which we derive register and read/write method names *)
  Context (prefix: string).
  
  (* Names of enqueue pointer and dequeue pointer *)
  Definition enqPtr: string := prefix ++ "enqPtr".
  Definition deqPtr: string := prefix ++ "deqPtr".
  
  (* Names of methods for interacting with the AsyncRegFile backing the FIFO *)
  Definition readName: string := prefix ++ "readName".
  Definition writeName: string := prefix ++ "writeName".
  
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  
  Local Definition fastModLen {ty} (w : Bit (size + 1) @# ty): Bit size @# ty :=
    UniBit (TruncLsb size 1) w.

  Definition isEmpty: ActionT ty Bool :=
    Read deq: Bit (size + 1) <- @^deqPtr;
    Read enq: Bit (size + 1) <- @^enqPtr;
    Ret (#deq == #enq).
  
  Definition isFull: ActionT ty Bool :=
    Read deq: Bit (size + 1) <- @^deqPtr;
    Read enq: Bit (size + 1) <- @^enqPtr;
    Ret ((#deq + $len) == #enq).
  
  Definition first: ActionT ty (Maybe k) := 
    LETA empty: Bool <- isEmpty;
    Read deq: Bit (size + 1) <- @^deqPtr;
    LET idx: Bit size <- (fastModLen #deq);
    Call dat: k <- readName(#idx: Bit size);
    Ret (STRUCT { "valid" ::= !#empty; "data" ::= #dat} : Maybe k @# ty).

  Definition deq: ActionT ty (Maybe k) :=
    LETA dat: Maybe k <- first;
    Read deq: Bit (size + 1) <- @^deqPtr;
    Write @^deqPtr: Bit (size + 1) <- #deq + (IF #dat @% "valid" then $1 else $0);
    Ret #dat.

  Definition enq (new: k @# ty): ActionT ty Bool :=
    Read enq: Bit (size + 1) <- @^enqPtr;
    LET idx: Bit size <- (fastModLen #enq);
    LETA full: Bool <- isFull;
    If !#full then (
      Call writeName(STRUCT { "addr" ::= #idx;
                              "data" ::= new } : WriteRq size k );
      Write @^enqPtr: Bit (size + 1) <- #enq + $1;
      Retv
    );
    Ret !#full.

  Definition flush: ActionT ty Void :=
    Write @^deqPtr: Bit (size + 1) <- $0;
    Write @^enqPtr: Bit (size + 1) <- $0;
    Retv.

  Definition asyncFifo: Fifo size := Build_Fifo size enqPtr deqPtr readName writeName isEmpty isFull first deq enq flush.
End AsyncFifo.
