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

    Definition ClientTagSz := Vector.fold_left Nat.max 0 clientTagSizes.
    Definition ClientTag := Bit ClientTagSz.

    Definition IdTag: Kind := STRUCT_TYPE { "id" :: Id;
                                            "tag" :: ClientTag }.

    Definition MemReq := STRUCT_TYPE { "tag" :: ServerTag;
                                       "data" :: reqK }.
  
    (* Action that allows us to make a request to physical memory *)
    Context (memReq: MemReq @# ty -> ActionT ty Bool).
    
    (* Per-client translator request action *)
    Open Scope kami_expr_scope.
    Definition clientReq (id: Fin.t numClients) (taggedReq: STRUCT_TYPE { "tag" :: Bit (Vector.nth clientTagSizes id);
                                                                          "req" :: reqK } @# ty): ActionT ty Bool :=
      LET newEntry <- STRUCT { "id" ::= $(proj1_sig (Fin.to_nat id));
                               "tag" ::= (ZeroExtendTruncLsb _ (taggedReq @% "tag") : ClientTag @# ty) };
      Read arb: Bool <- arbiter;
      Read freeArray: Array serverTagNum Bool <- freeArrayName;
      Nondet tag: ServerTag;
      LET tagFree: Bool <- !(#freeArray@[#tag]);
      If !#arb && #tagFree then (
        Write arbiter: Bool <- $$true;
        LETA reqOk: Bool <- memReq (STRUCT { "tag" ::=  #tag;
                                             "data" ::= taggedReq @% "req" } : MemReq @# ty);
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
  Definition memCallback (resp: MemResp @# ty): ActionT ty Void :=
    LET sTag: ServerTag <- resp @% "tag";
    Read freeArray: Array serverTagNum Bool <- freeArrayName;
    Read assocArray: Array serverTagNum IdTag <- assocArrayName;
    LET idtag: IdTag <- #assocArray@[#sTag];
    Write freeArrayName: Array serverTagNum Bool <- #freeArray@[#sTag <- $$false];
    LET respId: Id <- #idtag @% "id";
    LET respTag: ClientTag <- #idtag @% "tag";
    GatherActions (List.map (fun (id: Fin.t numClients) => 
                If $(proj1_sig (Fin.to_nat id)) == #respId then (
                   LETA _ <- (clientCallbacks id) (ZeroExtendTruncLsb _ (resp @% "tag") : Bit (Vector.nth clientTagSizes id) @# ty) (resp @% "data"); Retv
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
