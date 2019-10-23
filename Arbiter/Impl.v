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
    }.
  Section withParams.
    Context `{ArbiterImplParams}.
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
  
    Context (freelist: @FreeList ty serverTagNum).
    Definition nextToAlloc := freelist.(nextToAlloc).
    Definition alloc := freelist.(alloc).
    Definition free := freelist.(free).

    (* Action that allows us to make a request to physical memory *)
    Context (memReq: MemReq @# ty -> ActionT ty Bool).
    
    (* Per-client translator request action *)
    Open Scope kami_expr_scope.
    Definition clientReq (id: Fin.t numClients) (taggedReq: STRUCT_TYPE { "tag" :: Bit (Vector.nth clientTagSizes id);
                                                                          "req" :: reqK } @# ty): ActionT ty Bool :=
      Read arb: Bool <- arbiter;
      LETA serverTag: Maybe ServerTag <- nextToAlloc;
      If !#arb && #serverTag @% "valid" then (
        Write arbiter: Bool <- $$true;
        LETA reqOk: Bool <- memReq (STRUCT { "tag" ::=  #serverTag @% "data";
                                             "data" ::= taggedReq @% "req" } : MemReq @# ty);
        If #reqOk then (
            Call alistWrite(STRUCT { "addr" ::= (#serverTag @% "data");
                                     "data" ::= STRUCT { "id" ::= $(proj1_sig (Fin.to_nat id));
                                                         "tag" ::= (ZeroExtendTruncLsb _ (taggedReq @% "tag") : ClientTag @# ty) }
                                   }: WriteRq serverTagSz IdTag);
        LETA _ <- alloc (#serverTag @% "data");
        Retv);
      Ret #reqOk )
     else Ret $$false as retVal;
     Ret #retVal.

  (* What the "real" memory unit will call to respond to the tag
     translator; This is where the routing of responses to individual
     clients occurs. *)
  Definition memCallback (resp: MemResp @# ty): ActionT ty Void :=
    LET sTag: ServerTag <- resp @% "tag";
    Call idtag: IdTag <- alistRead(#sTag: ServerTag);
    LETA _ <- free #sTag;
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
End ArbiterImpl.
