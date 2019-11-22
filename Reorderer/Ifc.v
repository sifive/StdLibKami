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
    Record Reorderer: Type :=
      {
        handle: forall {ty}, ActionT ty Void;
        TranslatorResponse: Kind := STRUCT_TYPE { "id" :: ReqId; "resp" :: respK };
        reordererCallback {ty} (resp: ty TranslatorResponse): ActionT ty Void;
        req {ty} (p: ty reqK): ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                        "info" :: reqResK }
      }.
  End withParams.
End Reorderer.
