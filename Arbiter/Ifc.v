Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section Arbiter.
  Open Scope kami_expr_scope.
  Context {ty: Kind -> Type}.

  Class ArbiterParams :=
    {
      reqK: Kind;
      respK: Kind;
      serverTagNum: nat;
      numClients: nat;
      clientTagSizes: Vector.t nat numClients;
      clientCallbacks: forall (id: Fin.t numClients), (ty (Bit (Vector.nth clientTagSizes id))) -> ty respK -> ActionT ty Void;
    }.

  Section withParams.
    Context `{ArbiterParams}.
    Definition serverTagSz := Nat.log2_up serverTagNum.
    Definition ServerTag: Kind := Bit serverTagSz.
    Definition MemResp := STRUCT_TYPE { "tag" :: ServerTag;
                                        "data" :: respK }.
    Record Arbiter: Type :=
      {
        ClientReqGen : forall (id: Fin.t numClients), ty STRUCT_TYPE {"tag" :: Bit (Vector.nth clientTagSizes id);
                                                                      "req" :: reqK} -> ActionT ty Bool;
        memCallback: ty MemResp -> ActionT ty Void;
        arbiterRule: ActionT ty Void;
      }.
  End withParams.
End Arbiter.
