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
    := Read busy : Bool <- busyName;
       LET tag : (Tag clients) <- STRUCT {
                                      "id"  ::= $(proj1_sig (Fin.to_nat clientId));
                                      "tag" ::= ZeroExtendTruncLsb (maxClientTagSz clients) (#clientReq @% "tag")
                                    };
       If !#busy
         then
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
       Ret #ret.

  Local Definition callback
    (ty: Kind -> Type)
    (res: ty (InRes clients))
    :  ActionT ty Void
    := LET clientIdTag <- #res @% "tag";
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
                    clientHandleRes client clientRes;
                Retv)
           (getFins (numClients clients)))
         as _;
       Retv.

  Local Definition resetRule ty : ActionT ty Void
    := Write busyName : Bool <- $$false;
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
