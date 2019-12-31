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

  Record ArbiterClient (reqK respK : Kind)
    := {
         arbiterClientTagSz : nat;
         ArbiterClientTag := Bit arbiterClientTagSz;
         ArbiterClientReq
           := STRUCT_TYPE {
                "tag" :: ArbiterClientTag;
                "req" :: reqK
              };
         ArbiterClientRes
           := STRUCT_TYPE {
                "tag"  :: ArbiterClientTag;
                "resp" :: Maybe respK
              };
         arbiterClientHandleRes
           :  forall {ty}, ty ArbiterClientRes -> ActionT ty Void
       }.

  Class ArbiterParams :=
    {
      reqK : Kind;   (* request sent to a memory device - specifically MemDeviceReq *)
      respK : Kind;  (* data returned by a memory device - specifically Data. *)
      ImmRes : Kind; (* immediate response from a memory device - specicially Maybe MemErrorPkt. *)
      transactionTagSz : nat;
      clients : list (ArbiterClient reqK respK)
    }.

  Section withParams.
    Context `{ArbiterParams}.

    Definition arbiterNumClients := length clients.

    Definition arbiterClientReq (clientId : Fin.t arbiterNumClients)
      := ArbiterClientReq (nth_Fin clients clientId).

    Definition arbiterClientRes (clientId : Fin.t arbiterNumClients)
      := ArbiterClientRes (nth_Fin clients clientId).

    Definition arbiterNumTransactions := pow2 transactionTagSz.

    Definition ArbiterTransactionTag: Kind := Bit transactionTagSz.

    Definition ArbiterRouterReq
      := STRUCT_TYPE {
           "tag" :: ArbiterTransactionTag;
           "req" :: reqK
         }.

    Definition ArbiterRouterRes
      := STRUCT_TYPE {
           "tag" :: ArbiterTransactionTag;
           "resp" :: Maybe respK
         }.

    Definition ArbiterRouterImmRes
      := STRUCT_TYPE {
           "ready" :: Bool;
           "info"  :: ImmRes
         }.

    Definition ArbiterImmRes := ArbiterRouterImmRes.

    Record Arbiter
      := {
           regs : list RegInitT;

           sendReq
             (routerSendReq 
               : forall {ty},
                 ty ArbiterRouterReq ->
                 ActionT ty ArbiterRouterImmRes)
             : forall (clientId : Fin.t arbiterNumClients) {ty},
               ty (arbiterClientReq clientId) ->
               ActionT ty ArbiterImmRes;

           memCallback : forall {ty}, ty ArbiterRouterRes -> ActionT ty Void;

           arbiterRule : forall {ty}, ActionT ty Void;
         }.
  End withParams.
End Arbiter.
