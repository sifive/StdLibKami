Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section Arbiter.
  Open Scope kami_expr_scope.
  Class ArbiterParams :=
    {
      reqK: Kind;
      respK: Kind;
      serverTagSz: nat;
      serverTagNum: nat := pow2 serverTagSz;
      clientTagSizes: list nat;
      numClients: nat := List.length clientTagSizes;
      clientCallbacks: forall {ty} (id: Fin.t numClients), ty STRUCT_TYPE { "tag" :: (Bit (nth_Fin clientTagSizes id));
                                                                       "resp" :: respK } -> ActionT ty Void;
    }.

  Section withParams.
    Context `{ArbiterParams}.
    Definition ServerTag: Kind := Bit (Nat.log2_up serverTagNum).
    Definition MemResp := STRUCT_TYPE { "tag" :: ServerTag;
                                        "data" :: respK }.
    Record Arbiter: Type :=
      {
        clientReqGen : forall {ty} (id: Fin.t numClients), ty STRUCT_TYPE {"tag" :: Bit (nth_Fin clientTagSizes id);
                                                                                          "req" :: reqK} -> ActionT ty Bool;
        memCallback: forall {ty}, ty MemResp -> ActionT ty Void;
        arbiterRule: forall {ty}, ActionT ty Void;
      }.
  End withParams.
End Arbiter.
