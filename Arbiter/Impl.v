Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.FreeList.Ifc.
Require Import List.

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
      freelist: @FreeList arbiterNumTransactions;
    }.

  Section withParams.
    Context `{ArbiterImplParams}.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition clientIdSz := Nat.log2_up arbiterNumClients.
    Definition ClientId := Bit clientIdSz.

    Definition GenericClientTagSz
      := fold_left Nat.max
           (map
             (fun client : ArbiterClient _ _
               => arbiterClientTagSz client)
             clients)
           0.

    Definition GenericClientTag := Bit GenericClientTagSz.

    Definition ClientIdTag
      := STRUCT_TYPE {
           "id"  :: ClientId;
           "tag" :: GenericClientTag
         }.

    Section withTy.
      Definition nextToAlloc {ty: Kind -> Type} := @nextToAlloc _ freelist ty.
      Definition alloc {ty: Kind -> Type} := @alloc _ freelist ty.
      Definition free {ty: Kind -> Type}:= @free _ freelist ty.

      (* Per-client translator request action *)

      Open Scope kami_expr_scope.

      (*
        Casts transaction tags stored in the free list into
        ArbiterTransactionTags.
      *)
      Local Definition toTransactionTag
        (f : nat -> Type)
        (tag : f (Nat.log2_up arbiterNumTransactions))
        :  f transactionTagSz
        := eq_rect
             (Nat.log2_up arbiterNumTransactions)
             (fun k => f k)
             tag
             transactionTagSz
             (Nat.log2_up_pow2
               transactionTagSz
               (Nat.le_0_l transactionTagSz)).

      Local Definition fromTransactionTag
        (f : nat -> Type)
        (tag : f transactionTagSz)
        :  f (Nat.log2_up arbiterNumTransactions)
        := eq_rect_r f tag
             (Nat.log2_up_pow2
               transactionTagSz
               (Nat.le_0_l transactionTagSz)).

      Definition sendReq
        (routerSendReq
          : forall {ty},
            ty ArbiterRouterReq ->
            ActionT ty ArbiterRouterImmRes)
        (clientId : Fin.t arbiterNumClients)
        (ty : Kind -> Type)
        (clientReq : ty (arbiterClientReq clientId))
        :  ActionT ty ArbiterImmRes
        := Read busy : Bool <- arbiter;
           LETA transactionTag
             :  Maybe ArbiterTransactionTag
             <- toTransactionTag
                  (fun n => ActionT ty (Maybe (Bit n)))
                  nextToAlloc;
           If !#busy && #transactionTag @% "valid"
             then
               Write arbiter : Bool <- $$true;
               LET routerReq
                 :  ArbiterRouterReq
                 <- STRUCT {
                      "tag" ::= #transactionTag @% "data";
                      "req" ::= #clientReq @% "req"
                    };
               LETA routerImmRes
                 :  ArbiterRouterImmRes
                 <- routerSendReq routerReq;
               If #routerImmRes @% "ready"
                 then
                   LET clientIdTag
                     :  ClientIdTag
                     <- STRUCT {
                          "id"  ::= $(proj1_sig (Fin.to_nat clientId));
                          "tag" ::= ZeroExtendTruncLsb GenericClientTagSz (#clientReq @% "tag")
                        };
                   LET transaction
                     :  WriteRq transactionTagSz ClientIdTag
                     <- STRUCT {
                          "addr" ::= #transactionTag @% "data";
                          "data" ::= #clientIdTag
                        };
                   Call alistWrite (#transaction : WriteRq transactionTagSz ClientIdTag);
                   LET transactionTagData
                     :  ArbiterTransactionTag
                     <- #transactionTag @% "data";
                   alloc
                     (fromTransactionTag
                       (fun n => ty (Bit n))
                       transactionTagData);
               Ret #routerImmRes
             else
               Ret $$(getDefaultConst ArbiterImmRes)
             as result;
           Ret #result.

      (*
        What the "real" memory unit will call to respond to the tag
        translator; This is where the routing of responses to individual
        clients occurs.
      *)
      Definition memCallback
        (ty: Kind -> Type)
        (routerRes: ty ArbiterRouterRes)
        :  ActionT ty Void
        := LET transactionTag
             :  ArbiterTransactionTag
             <- #routerRes @% "tag";
           Call clientIdTag
             :  ClientIdTag
             <- alistRead (#transactionTag: ArbiterTransactionTag);
           LETA _
             <- free
                  (fromTransactionTag
                    (fun n => ty (Bit n))
                    transactionTag);
           GatherActions
             (map
               (fun (clientId: Fin.t arbiterNumClients)
                 => let client
                      :  ArbiterClient _ _
                      := nth_Fin clients clientId in 
                    If $(proj1_sig (Fin.to_nat clientId)) == (#clientIdTag @% "id")
                      then
                        LET clientRes
                          :  ArbiterClientRes client
                          <- STRUCT {
                               "tag"  ::= ZeroExtendTruncLsb (arbiterClientTagSz client) (#routerRes @% "tag");
                               "resp" ::= #routerRes @% "resp"
                             };
                        arbiterClientHandleRes client clientRes;
                    Retv)
               (getFins arbiterNumClients))
             as _;
           Retv.

      (* TODO: LLEE does this make sense? *)
      Definition arbiterRule ty : ActionT ty Void
        := Write arbiter : Bool <- $$false;
           Retv.

    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.

    Definition regs: list RegInitT := makeModule_regs ( Register arbiter: Bool <- false  ) ++ (FreeList.Ifc.regs freelist).

    Definition arbiterImpl
      := Build_Arbiter
           regs
           sendReq
           memCallback
           arbiterRule.

  End withParams.
End ArbiterImpl.
