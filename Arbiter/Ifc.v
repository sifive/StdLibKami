(*
  Routes multiple concurrent memory requests from Arbiter clients
  to a device router that can only accept one request at a time
  and routes the response callback to the correct client response
  handler.
*)
Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Require Import List.

Section Arbiter.
  Open Scope kami_expr_scope.

  Record ArbiterClient (reqK resK : Kind)
    := {
         clientTagSz : nat;
         ClientTag := Bit clientTagSz;
         ClientReq
           := STRUCT_TYPE {
                "tag" :: ClientTag;
                "req" :: reqK
              };
         ClientRes
           := STRUCT_TYPE {
                "tag"  :: ClientTag;
                "resp" :: Maybe resK
              };
         clientHandleRes
           :  forall {ty}, ty ClientRes -> ActionT ty Void
       }.

  Class ArbiterParams :=
    {
      reqK : Kind;   (* request sent to a memory device - specifically MemDeviceReq *)
      respK : Kind;  (* data returned by a memory device - specifically Data. *)
      ImmRes : Kind; (* immediate response from a memory device - specicially Maybe MemErrorPkt. *)
      numTransactions: nat;
      clients : list (ArbiterClient reqK respK)
    }.

  Section withParams.
    Context `{ArbiterParams}.

    Definition numClients := length clients.

    Definition clientTag (clientId : Fin.t numClients)
      := ClientTag (nth_Fin clients clientId).

    Definition clientReq (clientId : Fin.t numClients)
      := ClientReq (nth_Fin clients clientId).

    Definition transactionTagSz := Nat.log2_up numTransactions.

    Definition TransactionTag: Kind := Bit transactionTagSz.

    Definition ArbiterRouterReq
      := STRUCT_TYPE {
           "tag" :: TransactionTag;
           "req" :: reqK
         }.

    (* TODO: LLEE: for later - remove the Maybe from respK in all stdlibkami components. *)
    Definition ArbiterRouterRes
      := STRUCT_TYPE {
           "tag" :: TransactionTag;
           "resp" :: Maybe respK
         }.

    (* Immediate response from the Device Router *)
    Definition ArbiterImmRes
      := STRUCT_TYPE {
           "ready" :: Bool;
           "info"  :: ImmRes
         }.

    Class Arbiter
      := {
           regs : list RegInitT;
           regFiles : list RegFileBase;

           sendReq
             (routerSendReq 
               : forall {ty},
                 ty ArbiterRouterReq ->
                 ActionT ty ArbiterImmRes)
             : forall (clientId : Fin.t numClients) {ty},
               ty (clientReq clientId) ->
               ActionT ty ArbiterImmRes;

           memCallback : forall {ty}, ty ArbiterRouterRes -> ActionT ty Void;

           arbiterRule : forall {ty}, ActionT ty Void;
         }.
  End withParams.
End Arbiter.
