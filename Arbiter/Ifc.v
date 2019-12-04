Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section Arbiter.
  Open Scope kami_expr_scope.
  Class ArbiterParams :=
    {
      reqK: Kind;
      respK: Kind;
      reqResK: Kind;
      serverTagSz: nat;
      serverTagNum: nat := pow2 serverTagSz;
      clientTagSizes: list nat;
      numClients: nat := List.length clientTagSizes;
    }.

  Section withParams.
    Context `{ArbiterParams}.
    Definition ServerTag: Kind := Bit (Nat.log2_up serverTagNum).
    Definition MemReq := STRUCT_TYPE { "tag" :: ServerTag;
                                       "req" :: reqK }.
    Definition MemResp := STRUCT_TYPE { "tag" :: ServerTag;
                                        "data" :: respK }.
    Record Arbiter: Type :=
      {
        clientReqGen (memReq: forall {ty},
                         ty MemReq -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                               "info" :: reqResK }):
          forall (id: Fin.t numClients) {ty}, ty STRUCT_TYPE { "tag" :: Bit (nth_Fin clientTagSizes id);
                                                               "req" :: reqK } -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                                                                           "info" :: reqResK };
        memCallback (clientCallbacks: forall (id: Fin.t numClients) {ty},
                        ty STRUCT_TYPE { "tag" :: (Bit (nth_Fin clientTagSizes id));
                                         "resp" :: respK } -> ActionT ty Void): forall {ty}, ty MemResp -> ActionT ty Void;
        arbiterRule: forall {ty}, ActionT ty Void;
      }.
  End withParams.
End Arbiter.
