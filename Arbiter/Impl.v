Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section ArbiterImpl.
  Context `{ArbiterParams}.
  Class ArbiterImplParams :=
    {
      arbiter: string;
      (* Names of read/write names for the reg-file backing the
         associative array with which we will map server tags to client
         tags/IDs *)
      alistRead: string;
      alistWrite: string;
      freelist: @FreeList serverTagNum;
    }.
  Section withParams.
    Context `{ArbiterImplParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition IdSz: nat := Nat.log2_up numClients.
    Definition Id: Kind := Bit IdSz.

    Definition ClientTagSz := List.fold_left Nat.max clientTagSizes 0.
    Definition ClientTag := Bit ClientTagSz.

    Definition IdTag: Kind := STRUCT_TYPE { "id" :: Id;
                                            "tag" :: ClientTag }.
    Section withTy.
      Definition nextToAlloc {ty: Kind -> Type} := @nextToAlloc _ freelist ty.
      Definition alloc {ty: Kind -> Type} := @alloc _ freelist ty.
      Definition free {ty: Kind -> Type}:= @free _ freelist ty.

      (* Per-client translator request action *)
      Open Scope kami_expr_scope.
      Definition clientReq
                 (memReq: forall {ty},
                     ty MemReq ->
                     ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                              "info" :: reqResK })
                 (id: Fin.t numClients)
                 (ty: Kind -> Type)
                 (taggedReq: ty STRUCT_TYPE { "tag" :: Bit (nth_Fin clientTagSizes id);
                                                                               "req" :: reqK }): ActionT ty STRUCT_TYPE { "ready" :: Bool; "info" :: reqResK } :=
        Read arb: Bool <- arbiter;
        LETA serverTag: Maybe ServerTag <- nextToAlloc;
        LET mRq <- STRUCT { "tag" ::=  #serverTag @% "data";
                            "req" ::= #taggedReq @% "req" };
        LET sTagDat <- #serverTag @% "data";
        If !#arb && #serverTag @% "valid" then (
          Write arbiter: Bool <- $$true;
          LETA reqRes <- memReq mRq;
          If #reqRes @% "ready" then (
              Call alistWrite(STRUCT { "addr" ::= (#serverTag @% "data");
                                       "data" ::= STRUCT { "id" ::= $(proj1_sig (Fin.to_nat id));
                                                           "tag" ::= (ZeroExtendTruncLsb _ (#taggedReq @% "tag") : ClientTag @# ty) }
                                     }: WriteRq (Nat.log2_up serverTagNum) IdTag);
              LETA _ <- alloc sTagDat ;
              Retv);
          Ret #reqRes )
      else Ret STRUCT { "ready" ::= $$false;
                        "info" ::= $$(@getDefaultConst reqResK) } as retVal;
      Ret #retVal.

    (* What the "real" memory unit will call to respond to the tag
     translator; This is where the routing of responses to individual
     clients occurs. *)
      Definition memCallback
                 (clientCallbacks: forall (id: Fin.t numClients) {ty},
                     ty STRUCT_TYPE { "tag" :: (Bit (nth_Fin clientTagSizes id));
                                      "resp" :: Maybe respK } -> ActionT ty Void)
                 (ty: Kind -> Type)
                 (resp: ty MemResp): ActionT ty Void :=
        LET sTag: ServerTag <- #resp @% "tag";
        Call idtag: IdTag <- alistRead(#sTag: ServerTag);
        LETA _ <- free sTag;
        LET respId: Id <- #idtag @% "id";
        LET respTag: ClientTag <- #idtag @% "tag";
        GatherActions (List.map (fun (id: Fin.t numClients) => 
                                   LET clientTag: Bit (nth_Fin clientTagSizes id) <- ZeroExtendTruncLsb _ (#resp @% "tag");
                                     LET respDat <- #resp @% "resp";
                                     LET taggedResp <- STRUCT { "tag" ::= #clientTag;
                                                                "resp" ::= #respDat };
                                     If $(proj1_sig (Fin.to_nat id)) == #respId then (
                                     LETA _ <- (clientCallbacks id) taggedResp;
                                       Retv
                                   ); Retv
                                )
                                (getFins numClients)) as _; Retv.

      Definition arbiterRule ty: ActionT ty Void :=
        Write arbiter: Bool <- $$false;
        Retv.
    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    Definition regs: list RegInitT := makeModule_regs ( Register arbiter: Bool <- false  ) ++ (FreeList.Ifc.regs freelist).

    Definition arbiterImpl := Build_Arbiter
                                regs
                                clientReq
                                memCallback
                                arbiterRule.
  End withParams.
End ArbiterImpl.
