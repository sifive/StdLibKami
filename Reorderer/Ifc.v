Require Import Kami.All.
Section Reorderer.
  Class ReordererParams := {                            
      numReqId: nat;
      privModeK: Kind;                      
      pAddrK: Kind;
      vAddrK: Kind;
      mInstK: Kind;
      immResK: Kind;
    }.
  Section withParams.
    Context `{ReordererParams}.

    Definition reqIdSz := Nat.log2_up numReqId.
    Definition ReordererReqId := Bit reqIdSz.

    Definition ReordererReq
      := STRUCT_TYPE {
           "mode"  :: privModeK;
           "paddr" :: pAddrK;
           "vaddr" :: vAddrK
         }.

    Definition ReordererArbiterReq
      := STRUCT_TYPE {
           "tag" :: ReordererReqId;
           "req" :: pAddrK
         }.

    Definition ReordererImmRes
      := STRUCT_TYPE {
           "ready" :: Bool;
           "info"  :: immResK
         }.

    Definition ReordererArbiterRes
      := STRUCT_TYPE {
           "tag"  :: ReordererReqId;
           "resp" :: mInstK
         }.

    Definition ReordererRes
      := STRUCT_TYPE {
           "vaddr" :: vAddrK;
           "info"  :: immResK;
           "inst"  :: mInstK
           }.

    Definition ReordererStorage
      := STRUCT_TYPE {
           "vaddr" :: vAddrK;
           "info"  :: immResK
           }.

    Class Reorderer: Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        responseToPrefetcherRule (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void): forall {ty}, ActionT ty Void;
        callback {ty} (resp: ty ReordererArbiterRes): ActionT ty Void;
        sendReq
          ty
          (isError : immResK @# ty -> Bool @# ty)
          (memReq
            : ty ReordererArbiterReq ->
              ActionT ty ReordererImmRes)
          (p: ty ReordererReq)
          : ActionT ty Bool
      }.
  End withParams.
End Reorderer.
