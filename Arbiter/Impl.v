Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.FreeList.Ifc.

Section ArbiterImpl.
  Context `{ArbiterParams}.
  Context {ty: Kind -> Type}.
  Class ArbiterImplParams :=
    {
      arbiter: string;
      clients: list (@ClientData ty _);
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

    Definition IdSz: nat := Nat.log2_up (List.length clients).
    Definition Id: Kind := Bit IdSz.

    Definition ClientTagSz := List.fold_left Nat.max (List.map tagSz clients) 0.
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
    Definition clientReq (id: nat) (client: ClientData) (taggedReq: (@ClientReq ty _ client) @# ty): ActionT ty Bool :=
      Read arb: Bool <- arbiter;
      LETA serverTag: Maybe ServerTag <- nextToAlloc;
      If !#arb && #serverTag @% "valid" then (
        Write arbiter: Bool <- $$true;
        LETA reqOk: Bool <- memReq (STRUCT { "tag" ::=  #serverTag @% "data";
                                             "data" ::= taggedReq @% "req" } : MemReq @# ty);
        If #reqOk then (
            Call alistWrite(STRUCT { "addr" ::= (#serverTag @% "data");
                                     "data" ::= STRUCT { "id" ::= $id;
                                                         "tag" ::= (ZeroExtendTruncLsb _ (taggedReq @% "tag") : ClientTag @# ty) }
                                   }: WriteRq serverTagSz IdTag);
        LETA _ <- alloc;
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
    LET respId: Id <- #idtag @% "id";
    LET respTag: ClientTag <- #idtag @% "tag";
    GatherActions (List.map (fun (c: nat * ClientData) => 
                 If $(fst c) == #respId then (
                   LETA _ <- (callback (snd c)) (ZeroExtendTruncLsb _ (resp @% "tag") : Bit (tagSz (snd c)) @# ty) (resp @% "data"); Retv
                 ); Retv
              )
              (List.combine (seq 0 (List.length clients)) clients)) as _; Retv.

  Definition arbiterRule: ActionT ty Void :=
    Write arbiter: Bool <- $$false;
    Retv.

  Definition arbiterImpl := Build_Arbiter
                              clientReq
                              memCallback
                              arbiterRule.
  End withParams.
End ArbiterImpl.
