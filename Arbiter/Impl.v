Require Import Kami.All.
Require Import StdLibKami.Arbiter.Ifc.
Require Import StdLibKami.FreeList.Ifc.
Require Import List.

Section ArbiterImpl.
  Context {arbiterParams : ArbiterParams}.

  Local Definition arbiterBusyRegName := (Arbiter.Ifc.name ++ ".busy")%string.
  Local Definition arbiterAlistName   := (Arbiter.Ifc.name ++ ".alist")%string.
  Local Definition arbiterAlistReadName  := (Arbiter.Ifc.name ++ ".alistRead")%string.
  Local Definition arbiterAlistWriteName := (Arbiter.Ifc.name ++ ".alistWrite")%string.

  Instance freeListParams
    :  FreeListParams 
    := {|
         name := (Arbiter.Ifc.name ++ ".freelist")%string;
         tagSz := transactionTagSz;
       |}.

  Class ArbiterImplParams :=
    {
      freelist: @FreeList freeListParams;
    }.

  Section withParams.
    Context `{ArbiterImplParams}.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition clientIdSz := Nat.log2_up numClients.
    Definition ClientId := Bit clientIdSz.

    Definition genericClientTagSz
      := fold_left Nat.max
           (map
             (fun client : ArbiterClient _ _
               => clientTagSz client)
             clients)
           0.

    Definition genericClientTag := Bit genericClientTagSz.

    Definition ClientIdTag
      := STRUCT_TYPE {
           "id"  :: ClientId;
           "tag" :: genericClientTag
         }.

    Section withTy.
      Definition nextToAlloc {ty: Kind -> Type} := @nextToAlloc _ freelist ty.
      Definition alloc {ty: Kind -> Type} := @alloc _ freelist ty.
      Definition free {ty: Kind -> Type}:= @free _ freelist ty.

      (* Per-client translator request action *)

      Open Scope kami_expr_scope.

      Definition sendReq
        (isError : forall {ty}, immResK @# ty -> Bool @# ty)
        (routerSendReq
          : forall {ty},
            ty ArbiterRouterReq ->
            ActionT ty ArbiterImmRes)
        (clientId : Fin.t numClients)
        (ty : Kind -> Type)
        (clientReq : ty (clientReqK (nth_Fin clients clientId)))
        :  ActionT ty ArbiterImmRes
        := System [
             DispString _ "[Arbiter.sendReq]\n"
           ];
           Read busy : Bool <- arbiterBusyRegName;
           LETA transactionTag
             :  Maybe TransactionTag
             <- nextToAlloc;
           System [
             DispString _ "[Arbiter.sendReq] next available transaction tag\n";
             DispHex #transactionTag;
             DispString _ "\n"
           ];
           If !#busy && #transactionTag @% "valid"
             then
               System [
                 DispString _ "[Arbiter.sendReq] sending request.\n"
               ];
               Write arbiterBusyRegName : Bool <- $$true;
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
                          "tag" ::= ZeroExtendTruncLsb genericClientTagSz (#clientReq @% "tag")
                        };
                   System [
                     DispString _ "[Arbiter.sendReq] saving transaction and client id tag:\n";
                     DispHex #clientIdTag;
                     DispString _ "\n"
                   ];
                   WriteRf arbiterAlistWriteName (#transactionTag @% "data" : transactionTagSz ; #clientIdTag : ClientIdTag );
                   LET transactionTagData
                     :  TransactionTag
                     <- #transactionTag @% "data";
                   System [
                     DispString _ "[Arbiter.sendReq] allocating transaction tag:\n";
                     DispHex #transactionTagData;
                     DispString _ "\n"
                   ];
                   alloc transactionTagData;
               Ret #routerImmRes
             else
               Ret $$(getDefaultConst ArbiterImmRes)
             as result;
           System [
             DispString _ "[Arbiter.sendReq] result:";
             DispHex #result;
             DispString _ "\n"
           ];
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
        := System [
             DispString _ "[Arbiter.memCallback]\n"
           ];
           LET transactionTag
             :  TransactionTag
             <- #routerRes @% "tag";
           ReadRf clientIdTag
             :  ClientIdTag
             <- arbiterAlistReadName (#transactionTag: TransactionTag);
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
                          :  clientResK client
                          <- STRUCT {
                               "tag"  ::= ZeroExtendTruncLsb (clientTagSz client) (#routerRes @% "tag");
                               "resp" ::= #routerRes @% "resp"
                             };
                        System [
                          DispString _ "[Arbiter.memCallback] client res: ";
                          DispHex #clientRes;
                          DispString _ "\n"
                        ];
                        clientHandleRes client clientRes;
                    Retv)
               (getFins numClients))
             as _;
           Retv.

      (* TODO: LLEE does this make sense? *)
      Definition arbiterRule ty : ActionT ty Void
        := System [
             DispString _ "[Arbiter.arbiterRule]\n"
           ];
           Write arbiterBusyRegName : Bool <- $$false;
           Retv.

    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.

    Definition regs: list RegInitT
      := makeModule_regs
           (Register arbiterBusyRegName: Bool <- false) ++
           (@FreeList.Ifc.regs freeListParams freelist).

    (* TODO: LLEE: check *)
    Definition regFiles :=
      @Build_RegFileBase false 1 arbiterAlistName (Async [arbiterAlistReadName]) arbiterAlistWriteName numTransactions ClientIdTag (@RFNonFile _ _ None) ::
                         (@FreeList.Ifc.regFiles freeListParams freelist).

    Instance arbiterImpl
      :  Arbiter
      := {| Arbiter.Ifc.regs := regs ;
            Arbiter.Ifc.regFiles := regFiles ;
            Arbiter.Ifc.sendReq := sendReq ;
            Arbiter.Ifc.memCallback := memCallback ;
            Arbiter.Ifc.arbiterRule := arbiterRule |}.
  End withParams.
End ArbiterImpl.
