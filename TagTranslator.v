Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.

Section MemTagTranslator.
  Context (name: string).
  Context (ty: Kind -> Type).
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Context (respK: Kind).
  Context (reqK: Kind).
  Context (serverTagNum: nat).

  Definition serverTagSz := Nat.log2_up serverTagNum.

  Record ClientData: Type := {
                        tagSz: nat;
                        callback: Bit tagSz @# ty -> respK @# ty -> ActionT ty Void 
                      }.
  
  Context (clients: list ClientData).
  Definition IdSz: nat := Nat.log2_up (List.length clients).
  Definition Id: Kind := Bit IdSz.

  Definition ClientTagSz := List.fold_left Nat.max (List.map tagSz clients) 0.
  Definition ClientTag := Bit ClientTagSz.

  Definition ServerTag := Bit serverTagSz.

  Definition MemResp := STRUCT_TYPE { "tag" :: ClientTag;
                                      "data" :: respK }.

  Context (freelist: @FreeList ty serverTagNum).
  Definition alloc := (FreeList.Ifc.alloc freelist).
  Definition nextToAlloc := (FreeList.Ifc.nextToAlloc freelist).
  Definition free := (FreeList.Ifc.free freelist).

  (* Action that allows us to make a request to physical memory *)
  Context (memReq: Bit serverTagSz @# ty -> reqK @# ty -> ActionT ty Bool).
  
  (* Names of read/write names for the reg-file backing the
     associative array with which we will map server tags to client
     tags/IDs *)
  Context (alistRead alistWrite: string).
  
  (* Method name prefix for client callback methods *)
  Context (clientCallbackPrefix: string).

  Definition ClientReq (client: ClientData): Kind := STRUCT_TYPE { "tag" :: Bit (tagSz client);
                                                                   "req" :: reqK }.

  Definition IdTag: Kind := STRUCT_TYPE { "id" :: Id;
                                          "tag" :: ClientTag }.

  (* Per-client translator request action *)
  Definition clientReq (id: nat) (client: ClientData) (taggedReq: (ClientReq client) @# ty): ActionT ty Bool :=
    LETA serverTag: Maybe ServerTag <- nextToAlloc;
    If #serverTag @% "valid" then (
      LETA reqOk: Bool <- memReq (#serverTag @% "data") (taggedReq @% "req");
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
    LET sTag: ClientTag <- resp @% "tag";
    Call idtag: IdTag <- alistRead(#sTag: ClientTag);
    LET respId: Id <- #idtag @% "id";
    LET respTag: ClientTag <- #idtag @% "tag";
    GatherActions (List.map (fun (c: nat * ClientData) => 
                 If $(fst c) == #respId then (
                   LETA _ <- (callback (snd c)) (ZeroExtendTruncLsb _ (resp @% "tag") : Bit (tagSz (snd c)) @# ty) (resp @% "data"); Retv
                 ); Retv
              )
              (List.combine (seq 0 (List.length clients)) clients)) as _; Retv.
End MemTagTranslator.
