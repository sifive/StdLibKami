Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.

Class PrefetcherParams :=
  { PrivMode: Kind;
    PAddrSz: nat }.
                           

Section prefetcher.
  Context `{fifoTopParams : FifoTopParams}.
  Context `{PrefetcherParams}.

  Local Definition PAddr := Bit PAddrSz.

  Definition PrefetcherReq
    := STRUCT_TYPE {
         "mode"  :: PrivMode;
         "paddr" :: PAddr;
         "vaddr" :: VAddr
       }.

  Definition PrefetcherRes
    := STRUCT_TYPE {
         "vaddr" :: VAddr;
         "info"  :: ImmRes;
         "inst"  :: Maybe Inst
       }.

  Class Prefetcher: Type :=
    {
      regs: list RegInitT;
      regFiles : list RegFileBase;
      
      flush: forall {ty}, ActionT ty Void;

      (*
        Returns the address that needs to be fetched to retrieve the
        upper 16 bits of the current instruction's 32 bit word.
      *)
      getIsCompleting: forall {ty}, ActionT ty (Maybe VAddr);

      resetCompleting: forall {ty}, ActionT ty Void;

      isFull: forall {ty}, ActionT ty Bool;
      
      memCallback: forall {ty}, ty PrefetcherRes -> ActionT ty Void;

      fetchInstruction: forall {ty}, ActionT ty DeqRes;

      doPrefetch
        ty
        (memReq
          : ty PrefetcherReq ->
              ActionT ty Bool)
        : ty PrefetcherReq -> ActionT ty Bool;
    }.
End prefetcher.
