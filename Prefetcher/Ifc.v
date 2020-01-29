Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.

Class PrefetcherParams :=
  { PrivMode : Kind;
    PAddrSz : nat;
    VAddrSz : nat;
    CompInstSz : nat;
    ImmRes : Kind;
    isCompressed: forall ty, Bit CompInstSz @# ty -> Bool @# ty;
    isErr: forall ty, ImmRes @# ty -> Bool @# ty
  }.

Section Prefetcher.
  Context `{prefetcherParams: PrefetcherParams}.

  Local Definition PAddr    := Bit PAddrSz.
  Local Definition VAddr    := Bit VAddrSz.
  Local Definition CompInst := Bit CompInstSz.
  Local Definition InstSz   := CompInstSz + CompInstSz.
  Local Definition Inst     := Bit InstSz.

  Definition ShortVAddrSz := (VAddrSz - 2)%nat.

  Definition ShortVAddr := Bit ShortVAddrSz.

  Definition toFullVAddr {ty} (short: ShortVAddr @# ty): VAddr @# ty := ZeroExtendTruncLsb _ ({< short, $$(natToWord 2 0) >})%kami_expr.
  
  Definition toShortVAddr {ty} (long: VAddr @# ty): ShortVAddr @# ty := ZeroExtendTruncMsb _ (long)%kami_expr.
    
  Definition PrefetcherFifoEntry
    := STRUCT_TYPE {
         "vaddr" :: ShortVAddr;
         "info"  :: ImmRes;  
         "inst"  :: Maybe Inst
       }.

  Definition TopEntry: Kind
    := STRUCT_TYPE {
         "vaddr" :: ShortVAddr;
         "info"  :: ImmRes;
         "noErr" :: Bool;
         "upper" :: Maybe CompInst;
         "lower" :: Maybe CompInst
       }.
  
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

  (* if inst contains a compressed instruction the upper 16 bit contain arbitrary data. *)
  Definition DeqRes
    := STRUCT_TYPE {
         "notComplete" :: Bool;
         "vaddr" :: VAddr;
         "info"  :: ImmRes;
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
