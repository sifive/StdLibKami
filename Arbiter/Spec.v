Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Section ArbiterSpec.
  Context `{ArbiterParams}.
  Definition MemReq := STRUCT_TYPE { "tag" :: ArbiterTag;
                                     "req" :: reqK }.
  Class ArbiterSpecParams :=
    {
      arbiter: string;
      (* Names of read/write names for the reg-file backing the
         associative array with which we will map server tags to client
         tags/IDs *)
      alistRead: string;
      alistWrite: string;
      (* Name of the free array register *)
      freeArrayName: string;
      (* Name of the register which will store the array representing
         the mapping from server tags to ClientTag, ID tag pairs *)
      assocArrayName: string;
    }.
  Section withParams.
    Context `{ArbiterSpecParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition IdSz: nat := Nat.log2_up numClients.
    Definition Id: Kind := Bit IdSz.

    Definition ClientTagSz := List.fold_left Nat.max clientTagSizes 0.
    Definition ClientTag := Bit ClientTagSz.

    Definition IdTag: Kind := STRUCT_TYPE { "id" :: Id;
                                            "tag" :: ClientTag }.



    (* Per-client translator request action *)
    Open Scope kami_expr_scope.
    Section withTy.
      (* Context (ty: Kind -> Type). *)

      Definition clientReq
                 (memReq: forall {ty},
                     ty MemReq ->
                     ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                              "info" :: reqResK })
                 (id: Fin.t numClients)
                 (ty: Kind -> Type)
                 (taggedReq: ty STRUCT_TYPE { "tag" :: Bit (nth_Fin clientTagSizes id);
                                              "req" :: reqK }): ActionT ty STRUCT_TYPE { "ready" :: Bool; "info" :: reqResK } :=
        LET newEntry <- STRUCT { "id" ::= $(proj1_sig (Fin.to_nat id));
                                 "tag" ::= (ZeroExtendTruncLsb _ (#taggedReq @% "tag") : ClientTag @# ty) };
          Read arb: Bool <- arbiter;
          Read freeArray: Array arbiterTagNum Bool <- freeArrayName;
          Nondet tag: ArbiterTag;
          LET tagFree: Bool <- !(#freeArray@[#tag]);
          LET tagReq <- STRUCT { "tag" ::=  #tag;
                                 "req" ::= #taggedReq @% "req" };
          If !#arb && #tagFree then (
          Write arbiter: Bool <- $$true;
            LETA reqRes <- memReq (tagReq);
            If #reqRes @% "ready" then (
              Write freeArrayName: Array arbiterTagNum Bool <- #freeArray@[#tag <- $$true];
                Read assocArray: Array arbiterTagNum IdTag <- assocArrayName;
                Write assocArrayName: Array arbiterTagNum IdTag <- #assocArray@[#tag <- #newEntry];
                Retv
            );
            Ret #reqRes
        )
      else Ret STRUCT { "ready" ::= $$false;
                        "info" ::= $$(getDefaultConst reqResK) } as retVal;
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
        LET sTag: ArbiterTag <- #resp @% "tag";
          Read freeArray: Array arbiterTagNum Bool <- freeArrayName;
          Read assocArray: Array arbiterTagNum IdTag <- assocArrayName;
          LET idtag: IdTag <- #assocArray@[#sTag];
          Write freeArrayName: Array arbiterTagNum Bool <- #freeArray@[#sTag <- $$false];
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
    Definition regs: list RegInitT := makeModule_regs ( Register arbiter: Bool <- false ++
                                                        Register freeArrayName: Array arbiterTagNum Bool <- Default ++
                                                        Register assocArrayName: Array arbiterTagNum IdTag <- Default ).
                                                                               
    Definition arbiterImpl := Build_Arbiter
                                regs
                                clientReq
                                memCallback
                                arbiterRule.
  End withParams.
End ArbiterSpec.
