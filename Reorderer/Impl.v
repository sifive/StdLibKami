Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.Reorderer.Ifc.
Section Reorderer.
  Context `{ReordererParams}.
  Class ReordererImplParams :=
    {
      (* Methods for interacting with the response buffer (holding Maybe
     Insts). *)
      rfRead: string;
      rfWrite: string;
      (* methods for interacting with the address memory, which keeps
     track of the address each request corresponds to *)
      arfRead: string;
      arfWrite: string;
      handlingName: string;
      givingName: string;
    }.

  Section withParams.
    Context `{ReordererImplParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.
    
    Section withTy.

    (* Conceptual rule *)
   Definition handle
   (prefetcherCallback: forall {ty}, ty ReqResp -> ActionT ty Void)
   ty
   : ActionT ty Void :=
      Read handling: ReqId <- handlingName;
      Call MRes: Maybe respK <- rfRead(#handling: ReqId);
      Call req: reqK <- rfRead(#handling: ReqId);
      LET resp <- STRUCT { "req" ::= #req;
                           "resp" ::= #MRes @% "data" };
      If #MRes @% "valid" then (
        LETA _ <- prefetcherCallback (resp : ty ReqResp);
        Write handlingName <- #handling + $1;
        Retv
      );
      Retv.

   Definition ArbiterResponse: Kind := STRUCT_TYPE { "tag" :: ReqId; "resp" :: respK }.
  
   (* Action the arbiter will call when giving us (the reorderer) the
      response to a prior request *)
   Definition reordererCallback ty (resp: ty ArbiterResponse): ActionT ty Void :=
    LET idx: ReqId <- #resp @% "tag";
    LET res: respK <- #resp @% "resp";
    Call rfWrite(STRUCT { "addr" ::= #idx;
                          "data" ::= Valid #res } : WriteRq reqIdSz (Maybe respK));
    Retv.
    
   (* Action the prefetcher will ultimately use to make an order-preserving request for instructions at some address *)
   Definition req (memReq: forall {ty}, 
                ty ReordererReq ->
                ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                         "info" :: reqResK })
              {ty}
              (p: ty reqK): ActionT ty STRUCT_TYPE { "ready" :: Bool; "info" :: reqResK } :=
     Read giving: ReqId <- givingName;
     Read handling: ReqId <- handlingName;
     LET taggedReq <- STRUCT { "tag" ::= #giving;
                               "req" ::= #p };
     If (#giving + $1) != #handling then ( (* we can give a new reqid without forgetting the next one to service *)
        LETA res <- memReq (taggedReq);
        If #res @% "ready" then (
            Write givingName: ReqId <- #giving + $1;
            Call rfWrite(STRUCT { "addr" ::= #giving;
                                  "data" ::= Invalid } : WriteRq reqIdSz (Maybe respK));
            Call arfWrite(STRUCT { "addr" ::= #giving;
                                   "data" ::= #p } : WriteRq reqIdSz reqK);
            Retv
          );
        Ret #res
      ) else (
        Ret STRUCT { "ready" ::= $$false;
                     "info" ::= $$(getDefaultConst reqResK) }
      ) as ret;
      Ret #ret.
   End withTy.
    
   Definition implReorderer := Build_Reorderer handle reordererCallback req.
  End withParams.
End Reorderer.
