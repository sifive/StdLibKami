Require Import Kami.All.


Section Reorderer.
  Context (ty: Kind -> Type).
  Class ReordererParams := {
      reqK: Kind;
      resK: Kind;
      ReqRes: Kind := STRUCT_TYPE { "req" :: reqK;
                                    "res" :: resK };
      (* = log2 of how many requests the reorderer can have open at once *)
      reqIdSz: nat;
      ReqId: Kind := Bit reqIdSz;
    }.
  Section withParams.
    Context `{ReordererParams}.
    Record Reorderer: Type :=
      {
        handle: ActionT ty Void;
        TranslatorResponse: Kind := STRUCT_TYPE { "id" :: ReqId; "res" :: resK };
        reordererCallback (resp: ty TranslatorResponse): ActionT ty Void;
        req (p: ty reqK): ActionT ty Bool
      }.
  End withParams.
End Reorderer.
