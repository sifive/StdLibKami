Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.

Class PrefetcherParams :=
  { privMode : Kind;
    pAddrSz : nat;
    vAddrSz : nat;
    compInstSz : nat;
    immRes : Kind;
    isCompressed: forall ty, Bit compInstSz @# ty -> Bool @# ty;
    isErr: forall ty, immRes @# ty -> Bool @# ty
  }.

Section Prefetcher.
  Context `{prefetcherParams: PrefetcherParams}.

  Local Definition PAddr    := Bit pAddrSz.
  Local Definition VAddr    := Bit vAddrSz.
  Local Definition CompInst := Bit compInstSz.
  Local Definition InstSz   := compInstSz + compInstSz.
  Local Definition Inst     := Bit InstSz.

  Definition ShortvAddrSz := (vAddrSz - 2)%nat.

  Definition ShortVAddr := Bit ShortvAddrSz.

  Definition toFullVAddr {ty} (short: ShortVAddr @# ty): VAddr @# ty := ZeroExtendTruncLsb _ ({< short, $$(natToWord 2 0) >})%kami_expr.
  
  Definition toShortVAddr {ty} (long: VAddr @# ty): ShortVAddr @# ty := ZeroExtendTruncMsb _ (long)%kami_expr.
    
  Definition PrefetcherFifoEntry
    := STRUCT_TYPE {
         "vaddr" :: ShortVAddr;
         "info"  :: immRes;  
         "inst"  :: Maybe Inst
       }.

  Definition TopEntry: Kind
    := STRUCT_TYPE {
         "vaddr" :: ShortVAddr;
         "info"  :: immRes;
         "noErr" :: Bool;
         "upper" :: Maybe CompInst;
         "lower" :: Maybe CompInst
       }.
  
  Definition PrefetcherReq
    := STRUCT_TYPE {
         "mode"  :: privMode;
         "paddr" :: PAddr;
         "vaddr" :: VAddr
       }.

  Definition PrefetcherRes
    := STRUCT_TYPE {
         "vaddr" :: VAddr;
         "info"  :: immRes;
         "inst"  :: Maybe Inst
       }.

  (* if inst contains a compressed instruction the upper 16 bit contain arbitrary data. *)
  Definition DeqRes
    := STRUCT_TYPE {
         "notComplete" :: Bool;
         "vaddr" :: VAddr;
         "info"  :: immRes;
         "noErr" :: Bool;
         "inst"  :: Inst 
       }.

  Class Prefetcher: Type :=
    {
      regs: list RegInitT;
      regFiles : list RegFileBase;

      isFull: forall {ty}, ActionT ty Bool;
      doPrefetch ty (memReq: ty PrefetcherReq -> ActionT ty Bool): ty PrefetcherReq -> ActionT ty Bool;
      memCallback: forall {ty}, ty PrefetcherRes -> ActionT ty Void;
      fetchInstruction: forall {ty}, ActionT ty (Maybe DeqRes);
      clearTop: forall {ty}, ActionT ty Void;

      notCompleteDeqRule: forall {ty}, ActionT ty Void;
      transferRule: forall {ty}, ActionT ty Void;
    }.
End Prefetcher.
