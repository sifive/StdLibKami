Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Impl.

Section prefetcher.
  Context `{FifoTopParams}.
  Context (ImmRes: Kind). (* TODO: move? *)
  Variable PAddrSz : nat.

  Local Definition PAddr := Bit PAddrSz.

  Definition PrefetcherReq
    := STRUCT_TYPE {
         "vaddr" :: VAddr;
         "paddr" :: PAddr
       }.

  (*
    Note: isomorphic to ReordererReq.
  *)
  Definition PrefetcherReordererReq
    := STRUCT_TYPE {
         "req"  :: VAddr;
         "data" :: PAddr
       }.

  (*
    Note: isomorphic to ReordererImmRes.
    Note: also isomorphic to ArbiterImmRes.
  *)
  Definition PrefetcherReordererImmRes
    := STRUCT_TYPE {
         "ready" :: Bool;
         "info"  :: ImmRes (* Maybe Data *)
       }.

  (*
    Note: the entire request is returned by the reorderer so that
    the prefetcher can store the paddr for latter comparison.

    Note: isomorphic to ReordererRes.
  *)
  Definition PrefetcherReordererRes
    := STRUCT_TYPE {
         "req"  :: PrefetcherReordererReq;
         "resp" :: Maybe Inst
       }.

  Record Prefetcher: Type :=
    {
      regs: list RegInitT;
      
      flush: forall {ty}, ActionT ty Void;
      (*
        Returns the address that needs to be fetched to retrieve the
        upper 16 bits of the current instruction's 32 bit word.
      *)
      getIsCompleting: forall {ty}, ActionT ty (Maybe VAddr);

      (* Called by the Reorderer. *)
      memCallback: forall {ty}, ty PrefetcherReordererRes -> ActionT ty Void;

      (*
        Returns a 32 bit word that contains the current instruction
        and/or the virtual address that needs to be fetched to
        retrieve this instruction.
      *)
      fetchInstruction: forall {ty}, ActionT ty DeqRes;

      (*
        Accepts a function, [memReq], that accepts a physical
        address, verifies that we can load the given address,
        loads the address if possible, and returns an error code
        if appropriate; accepts a virtual address, the physical
        address associated with the virtual address, loads the
        data referenced by the virtual address, caches the data,
        and returns true iff the device accepted the load request.
      *)
      doPrefetch
        (memReq
          : forall {ty},
              ty PrefetcherReordererReq ->
              ActionT ty PrefetcherReordererImmRes)
        : forall {ty}, ty PrefetcherReq -> ActionT ty Bool;
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
