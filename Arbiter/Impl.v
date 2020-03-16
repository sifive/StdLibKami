Require Import Kami.AllNotations.
Require Import StdLibKami.Arbiter.Ifc.

Section Impl.
  Context {ifcParams : Ifc.Params}.
  Context (clients : Clients).

  Local Definition busyName := (name ++ ".busy")%string.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition sendReq
    (send: forall {ty}, ty (OutReq clients) -> ActionT ty (Maybe immResK))
    (clientId : Fin.t (numClients clients))
    (ty : Kind -> Type)
    (clientReq : ty (ClientReq (clientTagSz (nth_Fin (clientList clients) clientId))))
    :  ActionT ty (Maybe immResK)
    := System [
         DispString _ "[Arbiter.sendReq] clientReq: ";
         DispHex #clientReq;
         DispString _ "\n"
       ];
       Read busy : Bool <- busyName;
       LET tag : (Tag clients) <- STRUCT {
                                      "id"  ::= $(proj1_sig (Fin.to_nat clientId));
                                      "tag" ::= ZeroExtendTruncLsb (maxClientTagSz clients) (#clientReq @% "tag")
                                    };
       System [
         DispString _ "[Arbiter.sendReq] tag\n";
         DispHex #tag;
         DispString _ "\n"
       ];
       If !#busy
         then
           System [
             DispString _ "[Arbiter.sendReq] sending request.\n"
           ];
           Write busyName : Bool <- $$true;
           LET outReq : (OutReq clients) <- STRUCT {
                                                "tag" ::= #tag;
                                                "req" ::= #clientReq @% "req"
                                              };
           LETA immResM : Maybe immResK <- send outReq;
           Ret #immResM
         else
           Ret $$(getDefaultConst (Maybe immResK))
         as ret;
       System [
         DispString _ "[Arbiter.sendReq] result:";
         DispHex #ret;
         DispString _ "\n"
       ];
       Ret #ret.

  Local Definition callback
    (ty: Kind -> Type)
    (res: ty (InRes clients))
    :  ActionT ty Void
    := System [
         DispString _ "[Arbiter.memCallback] res: ";
         DispHex #res;
         DispString _ "\n"
       ];
       LET clientIdTag <- #res @% "tag";
       GatherActions
         (map
           (fun (clientId: Fin.t (numClients clients))
             => let client: Client _ := nth_Fin (clientList clients) clientId in 
                If $(proj1_sig (Fin.to_nat clientId)) == (#clientIdTag @% "id")
                  then
                    LET clientRes : clientResK client <- STRUCT {
                                                             "tag"  ::= ZeroExtendTruncLsb (clientTagSz client)
                                                                                           (#clientIdTag @% "tag");
                                                             "res" ::= #res @% "res"
                                                           };
                    System [
                      DispString _ "[Arbiter.memCallback] client res: ";
                      DispHex #clientRes;
                      DispString _ "\n"
                    ];
                    clientHandleRes client clientRes;
                Retv)
           (getFins (numClients clients)))
         as _;
       Retv.

  Local Definition resetRule ty : ActionT ty Void
    := System [
         DispString _ "[Arbiter.arbiterRule]\n"
       ];
       Write busyName : Bool <- $$false;
       Retv.

  Local Definition regs: list RegInitT
    := makeModule_regs
         (Register busyName: Bool <- false)%kami.

  Definition impl: (Ifc clients)
    := {| Arbiter.Ifc.regs := regs ;
          Arbiter.Ifc.regFiles := nil ;
          Arbiter.Ifc.sendReq := sendReq ;
          Arbiter.Ifc.callback := callback ;
          Arbiter.Ifc.resetRule := resetRule |}.
End Impl.
