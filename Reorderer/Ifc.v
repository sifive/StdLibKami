Require Import Kami.All.
Section Reorderer.
  Class ReordererParams := {                            
      numReqId: nat;
      PrivMode: Kind;                      
      PAddr: Kind;
      VAddr: Kind;
      MInst: Kind;
      ImmRes: Kind;
    }.
  Section withParams.
    Context `{ReordererParams}.

    Definition reqIdSz := Nat.log2_up numReqId.
    Definition ReordererReqId := Bit reqIdSz.

    Definition ReordererReq
      := STRUCT_TYPE {
           "mode"  :: PrivMode;
           "paddr" :: PAddr;
           "vaddr" :: VAddr
         }.

    Definition ReordererArbiterReq
      := STRUCT_TYPE {
           "tag" :: ReordererReqId;
           "req" :: PAddr
         }.

    Definition ReordererImmRes
      := STRUCT_TYPE {
           "ready" :: Bool;
           "info"  :: ImmRes
         }.

    Definition ReordererArbiterRes
      := STRUCT_TYPE {
           "tag"  :: ReordererReqId;
           "resp" :: MInst
         }.

    Definition ReordererRes
      := STRUCT_TYPE {
           "vaddr" :: VAddr;
           "info"  :: ImmRes;
           "inst"  :: MInst
           }.

    Definition ReordererStorage
      := STRUCT_TYPE {
           "vaddr" :: VAddr;
           "info"  :: ImmRes
           }.

    Class Reorderer: Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        responseToPrefetcher (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void): forall {ty}, ActionT ty Void;
        callback {ty} (resp: ty ReordererArbiterRes): ActionT ty Void;
        sendReq
          ty
          (isError : ImmRes @# ty -> Bool @# ty)
          (memReq
            : ty ReordererArbiterReq ->
              ActionT ty ReordererImmRes)
          (p: ty ReordererReq)
          : ActionT ty Bool
      }.
  End withParams.
End Reorderer.
