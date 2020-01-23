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
      alistName: string;
      alistRead: string;
      alistWrite: string;
      freelist: @FreeList numTransactions;
    }.

  Section withParams.
    Context `{ArbiterImplParams}.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition clientIdSz := Nat.log2_up numClients.
    Definition ClientId := Bit clientIdSz.

    Definition GenericClientTagSz
      := fold_left Nat.max
           (map
             (fun client : ArbiterClient _ _
               => clientTagSz client)
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

      Definition sendReq
        (isError : forall {ty}, ImmRes @# ty -> Bool @# ty)
        (routerSendReq
          : forall {ty},
            ty ArbiterRouterReq ->
            ActionT ty ArbiterImmRes)
        (clientId : Fin.t numClients)
        (ty : Kind -> Type)
        (clientReq : ty (clientReq clientId))
        :  ActionT ty ArbiterImmRes
        := Read busy : Bool <- arbiter;
           LETA transactionTag
             :  Maybe TransactionTag
             <- nextToAlloc;
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
                 :  ArbiterImmRes
                 <- routerSendReq routerReq;
               (* TODO: LLEE: accept an additional parameter that accepts an immres and returns true iff the immres signals an error. If error do not allocate resource (i.e. transaction tag. Note: this is a general error. Check other components as well. *) 
               If #routerImmRes @% "ready" && !(isError (#routerImmRes @% "info"))
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
                     :  TransactionTag
                     <- #transactionTag @% "data";
                   alloc transactionTagData;
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
             :  TransactionTag
             <- #routerRes @% "tag";
           Call clientIdTag
             :  ClientIdTag
             <- alistRead (#transactionTag: TransactionTag);
           LETA _
             <- free transactionTag;
           GatherActions
             (map
               (fun (clientId: Fin.t numClients)
                 => let client
                      :  ArbiterClient _ _
                      := nth_Fin clients clientId in 
                    If $(proj1_sig (Fin.to_nat clientId)) == (#clientIdTag @% "id")
                      then
                        LET clientRes
                          :  ClientRes client
                          <- STRUCT {
                               "tag"  ::= ZeroExtendTruncLsb (clientTagSz client) (#routerRes @% "tag");
                               "resp" ::= #routerRes @% "resp"
                             };
                        clientHandleRes client clientRes;
                    Retv)
               (getFins numClients))
             as _;
           Retv.

      (* TODO: LLEE does this make sense? *)
      Definition arbiterRule ty : ActionT ty Void
        := Write arbiter : Bool <- $$false;
           Retv.

    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.

    Definition regs: list RegInitT
      := makeModule_regs
           (Register arbiter: Bool <- false) ++
           (@FreeList.Ifc.regs numTransactions freelist).

    (* TODO: LLEE: check *)
    Definition regFiles :=
      @Build_RegFileBase false 1 alistName (Async [alistRead]) alistWrite numTransactions ClientIdTag (@RFNonFile _ _ None) ::
                         (@FreeList.Ifc.regFiles numTransactions freelist).

    Definition arbiterImpl
      :  Arbiter
      := {| Arbiter.Ifc.regs := regs ;
            Arbiter.Ifc.regFiles := regFiles ;
            Arbiter.Ifc.sendReq := sendReq ;
            Arbiter.Ifc.memCallback := memCallback ;
            Arbiter.Ifc.arbiterRule := arbiterRule |}.
  End withParams.
End ArbiterImpl.
