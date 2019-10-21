Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.

Section MemTagTranslator.
  Context (name: string).
  Context (ty: Kind -> Type).
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  Context (k: Kind).
  Context (reqK: Kind).

  Record ClientData: Type := {
                        tagSz: nat;
                        callback: Bit tagSz @# ty -> k @# ty -> ActionT ty Void 
                      }.
  
  Context (clients: list ClientData).
  Definition IdSz: nat := Nat.log2_up (List.length clients).
  Definition Id: Kind := Bit IdSz.

  Definition ServerTagSz := List.fold_left Nat.max (List.map tagSz clients) 0.
  Definition ServerTag := Bit ServerTagSz.

  Definition MemResp := STRUCT_TYPE { "tag" :: ServerTag;
                                      "data" :: k }.

  Context (freelist: @FreeList ty ServerTag).
  Definition alloc := (FreeList.Ifc.alloc freelist).
  Definition free := (FreeList.Ifc.free freelist).

  (* Action that allows us to make a request to physical memory *)
  Context (memReq: reqK @# ty -> ActionT ty Bool).
  
  (* Names of read/write names for the reg-file backing the
     associative array with which we will map server tags to client
     tags/IDs *)
  Context (alistRead alistWrite: string).
  
  (* Method name prefix for client callback methods *)
  Context (clientCallbackPrefix: string).

  (* Definition TagTranslatorResp := STRUCT_TYPE { "tag" :: ClientTag; *)
  (*                                               "data" :: Bit Rlen }. *)

  Definition ClientReq (client: ClientData): Kind := STRUCT_TYPE { "tag" :: Bit (tagSz client);
                                                                   "req" :: reqK }.

  Definition IdTag: Kind := STRUCT_TYPE { "id" :: Id;
                                          "tag" :: ServerTag }.

  (* Per-client translator request action *)
  Definition clientReq (id: nat) (client: ClientData) (taggedReq: (ClientReq client) @# ty): ActionT ty Bool :=
    LETA mTag <- alloc;
    If (#mTag @% "valid") then (
      LETA reqRet: Bool <- memReq (taggedReq @% "req": reqK @# ty);
      Ret #reqRet
      )
    else (
      Ret $$false
      ) as reqOk;
    If #reqOk then (
      Call alistWrite(STRUCT { "addr" ::= (#mTag @% "data");
                               "data" ::= STRUCT { "id" ::= $id;
                                                   "tag" ::= (ZeroExtendTruncLsb _ (taggedReq @% "tag") : ServerTag @# ty) }
                             }: WriteRq ServerTagSz IdTag);
      Retv
      )
    else (
      If (#mTag @% "valid") then (
        LETA _ <- free (#mTag @% "data");
        Retv
        );
      Retv
      );
    Ret ((#mTag @% "valid") && #reqOk).

  (* What the "real" memory unit will call to respond to the tag
     translator; This is where the routing of responses to individual
     clients occurs. *)
  Definition memCallback (resp: MemResp @# ty): ActionT ty Void :=
    LET sTag: ServerTag <- resp @% "tag";
    Call idtag: IdTag <- alistRead(#sTag: ServerTag);
    LET respId: Id <- #idtag @% "id";
    LET respTag: ServerTag <- #idtag @% "tag";
    GatherActions (List.map (fun (c: nat * ClientData) => 
                 If $(fst c) == #respId then (
                   LETA _ <- (callback (snd c)) (ZeroExtendTruncLsb _ (resp @% "tag") : Bit (tagSz (snd c)) @# ty) (resp @% "data"); Retv
                 ); Retv
              )
              (List.combine (seq 0 (List.length clients)) clients)) as _; Retv.
End MemTagTranslator.
