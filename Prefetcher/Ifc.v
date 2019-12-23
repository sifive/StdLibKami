Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Async.

Section prefetcher.
  Context `{FifoTopParams}.
  Context (reqResK: Kind). (* TODO: move? *)
  (* n.b.: these fields are so named to be consistent with the
     generic naming convention used in the reorderer *)
  Definition FullAddrMaybeInst: Kind := STRUCT_TYPE
                                     { "req" :: PAddr;
                                       "resp" :: Maybe Inst }.
  Record Prefetcher: Type :=
    {
      regs: list RegInitT;
      
      flush: forall {ty}, ActionT ty Void;
      getIsCompleting: forall {ty}, ActionT ty (Maybe PAddr);
      memCallback: forall {ty}, ty FullAddrMaybeInst -> ActionT ty Void;
      fetchInstruction: forall {ty}, ActionT ty DeqRes;
      doPrefetch (memReq: forall {ty},
                     ty PAddr -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                          "info" :: reqResK }):
        forall {ty}, ty PAddr -> ActionT ty Bool;
    }.

    (* The result type for a fetchInstruction:
       The bits encoded by the Maybe kinds in the fields have the following semantics:
       (Valid Addr, Valid Inst) |-> No problems; in the inst field is a full instruction corresponding to addr.
       (Valid Addr, Invalid Inst) |-> We only have the lower half of a 32 bit instruction in the top register,
                                   and need 16 bits at the address contiguous to addr to complete it;
                                   caller must prefetch addr returned.
       (Invalid Addr, Invalid Inst) |-> The Fifo + Top is empty.
       (Invalid Addr, Valid 0) |-> There was a device access exception for the address
                                   (even though it says Invalid, the address contains useful information);
                                   the client should handle an access exception for that address in this case
     *)
    (* Definition DeqRes: Kind := STRUCT_TYPE { "addr" :: Maybe PAddr ; *)
    (*                                          "inst" :: Maybe Inst }. *)
End prefetcher.
