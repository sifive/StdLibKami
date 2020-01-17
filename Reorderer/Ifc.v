Require Import Kami.All.
Section Reorderer.
  Class ReordererParams := {
      PAddr: Kind;
      VAddr: Kind;
      MInst: Kind;
      ImmRes: Kind;
      (* = log2 of how many requests the reorderer can have open at once *)
      reqIdSz: nat;
    }.
  Section withParams.
    Context `{ReordererParams}.

    Definition ReordererReqId := Bit reqIdSz.
    Definition ReordererPtr := Bit (reqIdSz + 1).

    Definition ReordererReq
      := STRUCT_TYPE {
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
           "inst"  :: MInst
         }.

    Class Reorderer: Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        responseToPrefetcher (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void): forall {ty}, ActionT ty Void;
        callback {ty} (resp: ty ReordererArbiterRes): ActionT ty Void;
        sendReq
          ty
          (memReq
            : ty ReordererArbiterReq ->
              ActionT ty ReordererImmRes)
          (p: ty ReordererReq)
          : ActionT ty ReordererImmRes
      }.
  End withParams.
End Reorderer.
