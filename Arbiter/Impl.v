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

  Local Definition hasResps
        (first: forall {ty}, ActionT ty (Maybe (InRes clients)))
        (clientId: Fin.t (numClients clients))
        (ty: Kind -> Type)
    : ActionT ty Bool
    := LETA res <- first;
       let client: Client _ := nth_Fin (clientList clients) clientId in
       Ret (#res @% "valid" && $(proj1_sig (Fin.to_nat clientId)) == #res @% "data" @% "tag" @% "id").
         
  Local Definition getResps
        (first: forall {ty}, ActionT ty (Maybe (InRes clients)))
        (deq: forall {ty}, ActionT ty (Maybe (InRes clients)))
        (clientId: Fin.t (numClients clients))
        (ty: Kind -> Type)
    : ActionT ty (Maybe (clientResK (nth_Fin (clientList clients) clientId)))
    := LETA res <- first;
       let client: Client _ := nth_Fin (clientList clients) clientId in
       If (#res @% "valid" && $(proj1_sig (Fin.to_nat clientId)) == #res @% "data" @% "tag" @% "id")
       then (
         LETA _ <- deq;
         LET clientRes : clientResK client <- STRUCT {
                                                  "tag"  ::= ZeroExtendTruncLsb (clientTagSz client) (#res @% "data" @% "tag" @% "tag");
                                                  "res" ::= #res @% "data" @% "res"
                                                };
         Ret (STRUCT { "valid" ::= $$true;
                       "data"  ::= #clientRes} : Maybe (clientResK client) @# ty) )
       else Ret (Invalid: Maybe (clientResK client) @# ty) as res;
       Ret #res.
         
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
          Arbiter.Ifc.hasResps := hasResps ;
          Arbiter.Ifc.getResps := getResps ;
          Arbiter.Ifc.resetRule := resetRule |}.
End Impl.
