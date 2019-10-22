Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section Arbiter.
  Open Scope kami_expr_scope.
  Context {ty: Kind -> Type}.

  Class ArbiterParams :=
    {
      reqK: Kind;
      respK: Kind;
      serverTagNum: nat
    }.

  Section withParams.
    Context `{ArbiterParams}.
    Definition serverTagSz := Nat.log2_up serverTagNum.
    Definition ServerTag: Kind := Bit serverTagSz.
    Definition MemResp := STRUCT_TYPE { "tag" :: ServerTag;
                                        "data" :: respK }.
    Record ClientData: Type :=
      {
        tagSz: nat;
        callback: Bit tagSz @# ty -> respK @# ty -> ActionT ty Void 
      }.
    Definition ClientReq (client: ClientData): Kind := STRUCT_TYPE { "tag" :: Bit (tagSz client);
                                                                     "req" :: reqK }.
    Record Arbiter: Type :=
      {
        ClientReqGen : nat -> forall (client : ClientData), (ClientReq client) @# ty -> ActionT ty Bool;
        memCallback: MemResp @# ty -> ActionT ty Void;
        arbiterRule: ActionT ty Void; (* TODO: really need to expose this? *)
      }.
  End withParams.
End Arbiter.
