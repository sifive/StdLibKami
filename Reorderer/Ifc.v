Require Import Kami.All.
Section Reorderer.
  Class ReordererParams := {
      reqK: Kind;
      reqDataK: Kind; (* additional data to track for the request. Specifically the physical address assocated with the request. *)
      respK: Kind;
      ImmRes: Kind;
      (* = log2 of how many requests the reorderer can have open at once *)
      reqIdSz: nat;
    }.
  Section withParams.
    Context `{ReordererParams}.

    Definition ReordererReqId := Bit reqIdSz.

    Definition ReordererReq
      := STRUCT_TYPE {
           "req"  :: reqK;    (* paddr *)
           "data" :: reqDataK (* vaddr *)
         }.

    Definition ReordererArbiterReq
      := STRUCT_TYPE {
           "tag" :: ReordererReqId;
           "req" :: reqK
         }.

    Definition ReordererArbiterImmRes
      := STRUCT_TYPE {
           "ready" :: Bool;
           "info"  :: ImmRes
         }.

    Definition ReordererImmRes := ReordererArbiterImmRes.

    Definition ReordererArbiterRes
      := STRUCT_TYPE {
           "tag"  :: ReordererReqId;
           "resp" :: respK
         }.

    (*
      TODO: return the context data stored sent in ReordererReq.data
      with the request. This is needed because the prefetcher does
      not save the virtual address associated with the request before
      sending the request. Consequently, the Reorderer must return
      the virtual address associated with the request response so
      that the prefetcher can save it in its cache.

      TODO: LLEE change req to just VAddr. (Not done see above comment)
    *)
    Definition ReordererRes
      := STRUCT_TYPE {
           "req"  :: ReordererReq;
           "resp" :: respK
         }.

    Class Reorderer: Type :=
      {
        regs: list RegInitT;
        handle (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void): forall {ty}, ActionT ty Void;
        reordererCallback {ty} (resp: ty ReordererArbiterRes): ActionT ty Void;
        sendReq
          (memReq
            : forall {ty}, 
              ty ReordererArbiterReq ->
              ActionT ty ReordererArbiterImmRes)
          {ty} 
          (p: ty ReordererReq)
          : ActionT ty ReordererImmRes
      }.
  End withParams.
End Reorderer.
