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
         clientTag := Bit clientTagSz;
         clientReq
           := STRUCT_TYPE {
                "tag" :: clientTag;
                "req" :: reqK
              };
         clientRes
           := STRUCT_TYPE {
                "tag"  :: clientTag;
                "resp" :: Maybe resK
              };
         clientHandleRes
           :  forall {ty}, ty clientRes -> ActionT ty Void
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
             (isError : forall {ty}, ImmRes @# ty -> Bool @# ty)
             (routerSendReq 
               : forall {ty},
                 ty ArbiterRouterReq ->
                 ActionT ty ArbiterImmRes)
             : forall (clientId : Fin.t numClients) {ty},
               ty (clientReq (nth_Fin clients clientId)) ->
               ActionT ty ArbiterImmRes;

           memCallback : forall {ty}, ty ArbiterRouterRes -> ActionT ty Void;

           arbiterRule : forall {ty}, ActionT ty Void;
         }.
  End withParams.
End Arbiter.
