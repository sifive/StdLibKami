Require Import Kami.All.
Section Reorderer.
  Class ReordererParams := {
      reqK: Kind;
      respK: Kind;
      ReqResp: Kind := STRUCT_TYPE { "req" :: reqK;
                                     "resp" :: respK };
      reqResK: Kind;
      (* = log2 of how many requests the reorderer can have open at once *)
      reqIdSz: nat;
      ReqId: Kind := Bit reqIdSz;
    }.
  Section withParams.
    Context `{ReordererParams}.
    Definition ReordererReq := STRUCT_TYPE { "tag" :: ReqId;
                                             "req" :: reqK }.
                                
    Record Reorderer: Type :=
      {
        regs: list RegInitT;
        
        handle (prefetcherCallback: forall {ty}, ty ReqResp -> ActionT ty Void): forall {ty}, ActionT ty Void;
        ArbiterResponse: Kind := STRUCT_TYPE { "tag" :: ReqId; "resp" :: respK };
        reordererCallback {ty} (resp: ty ArbiterResponse): ActionT ty Void;
        req (memReq: forall {ty}, 
                ty ReordererReq ->
                ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                         "info" :: reqResK })
            {ty} 
            (p: ty reqK): ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                   "info" :: reqResK }
      }.
  End withParams.
End Reorderer.
