Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section ArbiterImpl.
  Context `{ArbiterParams}.
  Definition MemReq := STRUCT_TYPE { "tag" :: ServerTag;
                                     "data" :: reqK }.
  Class ArbiterImplParams :=
    {
      arbiter: string;
      (* Names of read/write names for the reg-file backing the
         associative array with which we will map server tags to client
         tags/IDs *)
      alistRead: string;
      alistWrite: string;
      freelist: @FreeList serverTagNum;
      (* Action that allows us to make a request to physical memory *)
      memReq: forall {ty}, ty MemReq -> ActionT ty Bool
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
      Context (ty: Kind -> Type).
      (* @vmurali: here is the issue with this scheme *)
      Definition nextToAlloc := @nextToAlloc _ freelist ty.
      Definition alloc := @alloc _ freelist ty.
      Definition free := @free _ freelist ty.

      (* Per-client translator request action *)
      Open Scope kami_expr_scope.
      Definition clientReq (id: Fin.t numClients) (taggedReq: ty STRUCT_TYPE { "tag" :: Bit (nth_Fin clientTagSizes id);
                                                                               "req" :: reqK }): ActionT ty Bool :=
        Read arb: Bool <- arbiter;
          LETA serverTag: Maybe ServerTag <- nextToAlloc;
          LET mRq <- STRUCT { "tag" ::=  #serverTag @% "data";
                              "data" ::= #taggedReq @% "req" };
          LET sTagDat <- #serverTag @% "data";
          If !#arb && #serverTag @% "valid" then (
             Write arbiter: Bool <- $$true;
             LETA reqOk: Bool <- memReq mRq;
             If #reqOk then (
                 Call alistWrite(STRUCT { "addr" ::= (#serverTag @% "data");
                                          "data" ::= STRUCT { "id" ::= $(proj1_sig (Fin.to_nat id));
                                                              "tag" ::= (ZeroExtendTruncLsb _ (#taggedReq @% "tag") : ClientTag @# ty) }
                                        }: WriteRq (Nat.log2_up serverTagNum) IdTag);
                 LETA _ <- alloc sTagDat ;
                 Retv);
             Ret #reqOk )
      else Ret $$false as retVal;
      Ret #retVal.

    (* What the "real" memory unit will call to respond to the tag
     translator; This is where the routing of responses to individual
     clients occurs. *)
      Definition memCallback (resp: ty MemResp): ActionT ty Void :=
        LET sTag: ServerTag <- #resp @% "tag";
        Call idtag: IdTag <- alistRead(#sTag: ServerTag);
        LETA _ <- free sTag;
        LET respId: Id <- #idtag @% "id";
        LET respTag: ClientTag <- #idtag @% "tag";
        GatherActions (List.map (fun (id: Fin.t numClients) => 
                                   LET clientTag: Bit (nth_Fin clientTagSizes id) <- ZeroExtendTruncLsb _ (#resp @% "tag");
                                     LET respDat <- #resp @% "data";
                                     LET taggedResp <- STRUCT { "tag" ::= #clientTag;
                                                                "resp" ::= #respDat };
                                     If $(proj1_sig (Fin.to_nat id)) == #respId then (
                                     LETA _ <- (clientCallbacks id) taggedResp;
                                       Retv
                                   ); Retv
                                )
                                (getFins numClients)) as _; Retv.

      Definition arbiterRule: ActionT ty Void :=
        Write arbiter: Bool <- $$false;
        Retv.
    End withTy.
    Definition arbiterImpl := Build_Arbiter
                                clientReq
                                memCallback
                                arbiterRule.
  End withParams.  
End ArbiterImpl.
