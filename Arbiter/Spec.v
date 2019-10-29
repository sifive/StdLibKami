Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Section ArbiterSpec.
  Context `{ArbiterParams}.
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
      assocArrayName: string
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

    Definition MemReq := STRUCT_TYPE { "tag" :: ServerTag;
                                       "data" :: reqK }.
  
    (* Action that allows us to make a request to physical memory *)
    Context (memReq: ty MemReq -> ActionT ty Bool).
    
    (* Per-client translator request action *)
    Open Scope kami_expr_scope.
    Definition clientReq (id: Fin.t numClients) (taggedReq: ty STRUCT_TYPE { "tag" :: Bit (nth_Fin clientTagSizes id);
                                                                             "req" :: reqK }): ActionT ty Bool :=
      LET newEntry <- STRUCT { "id" ::= $(proj1_sig (Fin.to_nat id));
                               "tag" ::= (ZeroExtendTruncLsb _ (#taggedReq @% "tag") : ClientTag @# ty) };
      Read arb: Bool <- arbiter;
      Read freeArray: Array serverTagNum Bool <- freeArrayName;
      Nondet tag: ServerTag;
      LET tagFree: Bool <- !(#freeArray@[#tag]);
      LET tagReq <- STRUCT { "tag" ::=  #tag;
                             "data" ::= #taggedReq @% "req" };
      If !#arb && #tagFree then (
        Write arbiter: Bool <- $$true;
        LETA reqOk: Bool <- memReq (tagReq);
        If #reqOk then (
            Write freeArrayName: Array serverTagNum Bool <- #freeArray@[#tag <- $$true];
            Read assocArray: Array serverTagNum IdTag <- assocArrayName;
            Write assocArrayName: Array serverTagNum IdTag <- #assocArray@[#tag <- #newEntry];
            Retv
          );
        Ret #reqOk
      )
    else Ret $$false as retVal;
    Ret #retVal.

  (* What the "real" memory unit will call to respond to the tag
     translator; This is where the routing of responses to individual
     clients occurs. *)
  Definition memCallback (resp: ty MemResp): ActionT ty Void :=
    LET sTag: ServerTag <- #resp @% "tag";
    Read freeArray: Array serverTagNum Bool <- freeArrayName;
    Read assocArray: Array serverTagNum IdTag <- assocArrayName;
    LET idtag: IdTag <- #assocArray@[#sTag];
    Write freeArrayName: Array serverTagNum Bool <- #freeArray@[#sTag <- $$false];
    LET respId: Id <- #idtag @% "id";
    LET respTag: ClientTag <- #idtag @% "tag";
    GatherActions (List.map (fun (id: Fin.t numClients) => 
                LET clientTag: Bit (nth_Fin clientTagSizes id) <- ZeroExtendTruncLsb _ (#resp @% "tag");
                LET respDat <- #resp @% "data";
                If $(proj1_sig (Fin.to_nat id)) == #respId then (
                   LETA _ <- (clientCallbacks id) clientTag respDat; Retv
                 ); Retv
              )
              (getFins numClients)) as _; Retv.

  Definition arbiterRule: ActionT ty Void :=
    Write arbiter: Bool <- $$false;
    Retv.

  Definition arbiterImpl := Build_Arbiter
                              clientReq
                              memCallback
                              arbiterRule.
  End withParams.
End ArbiterSpec.
