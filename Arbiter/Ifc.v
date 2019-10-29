Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section Arbiter.
  Open Scope kami_expr_scope.
  Context {ty: Kind -> Type}.
  Class ArbiterParams :=
    {
      reqK: Kind;
      respK: Kind;
      serverTagSz: nat;
      serverTagNum: nat := pow2 serverTagSz;
      (* TODO: change to list of nats; investigate possible problems
         with this *)
      clientTagSizes: list nat;
      numClients: nat := List.length clientTagSizes;
      clientCallbacks: forall (id: Fin.t numClients), (ty (Bit (nth_Fin clientTagSizes id))) -> ty respK -> ActionT ty Void;
    }.

  Section withParams.
    Context `{ArbiterParams}.
    Definition ServerTag: Kind := Bit (Nat.log2_up serverTagNum).
    Definition MemResp := STRUCT_TYPE { "tag" :: ServerTag;
                                        "data" :: respK }.
    Record Arbiter: Type :=
      {
        clientReqGen : forall (id: Fin.t numClients), ty STRUCT_TYPE {"tag" :: Bit (nth_Fin clientTagSizes id);
                                                                      "req" :: reqK} -> ActionT ty Bool;
        memCallback: ty MemResp -> ActionT ty Void;
        arbiterRule: ActionT ty Void;
      }.
  End withParams.
End Arbiter.
