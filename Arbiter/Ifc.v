Require Import Kami.AllNotations.
Require Import List.

Section Ifc.
  Record Client (outResK : Kind)
    := { clientTagSz : nat;
         clientResK := STRUCT_TYPE {
                           "tag" :: Bit clientTagSz;
                           "res" :: outResK
                         };
       }.

  Record Clients := { outResK: Kind;
                      clientList: list (Client outResK) }.

  Class Params :=
    {
      name : string;
      inReqK : Kind;
      immResK : Kind;
      isError : forall {ty}, immResK @# ty -> Bool @# ty;
    }.

  Context {params: Params}.
  Context (clients : Clients).

  Definition numClients := length (clientList clients).

  Definition clientIdSz := Nat.log2_up numClients.
  Definition ClientId := Bit clientIdSz.

  Definition maxClientTagSz
    := fold_left Nat.max
         (map
           (fun client : Client _
             => clientTagSz client)
           (clientList clients))
         0.

  Definition MaxClientTag := Bit maxClientTagSz.

  Definition Tag
    := STRUCT_TYPE {
         "id"  :: ClientId;
         "tag" :: MaxClientTag
       }.
  
  Definition ClientReq clientTagSz := STRUCT_TYPE {
                                          "tag" :: Bit clientTagSz;
                                          "req" :: inReqK
                                        }.
  
  Definition OutReq := STRUCT_TYPE {
                           "tag" :: Tag;
                           "req" :: inReqK
                         }.

  Definition InRes := STRUCT_TYPE {
                          "tag" :: Tag;
                          "res" :: (outResK clients)
                        }.

  Record Ifc
    := {
         regs : list RegInitT;
         regFiles : list RegFileBase;

         sendReq (send : forall {ty}, ty OutReq -> ActionT ty (Maybe immResK))
         : forall (clientId : Fin.t numClients) {ty},
             ty (ClientReq (clientTagSz (nth_Fin (clientList clients) clientId))) -> ActionT ty (Maybe immResK);

         hasResps (first: forall {ty}, ActionT ty (Maybe InRes))
         : forall (clientId: Fin.t numClients) {ty},
             ActionT ty Bool;

         getResps (first: forall {ty}, ActionT ty (Maybe InRes))
                  (deq: forall {ty}, ActionT ty Bool)
         : forall (clientId: Fin.t numClients) {ty},
             ActionT ty (Maybe (clientResK (nth_Fin (clientList clients) clientId)));

         resetRule : forall {ty}, ActionT ty Void;
       }.
End Ifc.
