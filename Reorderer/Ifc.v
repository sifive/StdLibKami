Require Import Kami.All.
Section Reorderer.
  Class ReordererParams := {                            
      numReqId: nat;
      privModeT: Kind;                      
      pAddrT: Kind;
      vAddrT: Kind;
      mInstT: Kind;
      immResT: Kind;
    }.
  Section withParams.
    Context `{ReordererParams}.

    Definition reqIdSz := Nat.log2_up numReqId.
    Definition ReordererReqId := Bit reqIdSz.

    Definition ReordererReq
      := STRUCT_TYPE {
           "mode"  :: privModeT;
           "paddr" :: pAddrT;
           "vaddr" :: vAddrT
         }.

    Definition ReordererArbiterReq
      := STRUCT_TYPE {
           "tag" :: ReordererReqId;
           "req" :: pAddrT
         }.

    Definition ReordererImmRes
      := STRUCT_TYPE {
           "ready" :: Bool;
           "info"  :: immResT
         }.

    Definition ReordererArbiterRes
      := STRUCT_TYPE {
           "tag"  :: ReordererReqId;
           "resp" :: mInstT
         }.

    Definition ReordererRes
      := STRUCT_TYPE {
           "vaddr" :: vAddrT;
           "info"  :: immResT;
           "inst"  :: mInstT
           }.

    Definition ReordererStorage
      := STRUCT_TYPE {
           "vaddr" :: vAddrT;
           "info"  :: immResT
           }.

    Class Reorderer: Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        responseToPrefetcherRule (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void): forall {ty}, ActionT ty Void;
        callback {ty} (resp: ty ReordererArbiterRes): ActionT ty Void;
        sendReq
          ty
          (isError : immResT @# ty -> Bool @# ty)
          (memReq
            : ty ReordererArbiterReq ->
              ActionT ty ReordererImmRes)
          (p: ty ReordererReq)
          : ActionT ty Bool
      }.
  End withParams.
End Reorderer.
