Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.

Section Reorderer.
  Context (ty: Kind -> Type).
  Class ReordererParams :=
    {
      reqK: Kind;
      resK: Kind;
      ReqRes: Kind := STRUCT_TYPE { "req" :: reqK;
                                    "res" :: resK };
      reqIdSz: nat;
      ReqId: Kind := Bit reqIdSz;
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
      
      prefetcherCallback: ty ReqRes -> ActionT ty Void;
      ReordererReq := STRUCT_TYPE { "tag" :: ReqId;
                                    "req" :: reqK };
      memReq: ty ReordererReq -> ActionT ty Bool
    }.

  Section withParams.
    Context `{ReordererParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (* Conceptual rule *)
   Definition handle: ActionT ty Void :=
      Read handling: ReqId <- handlingName;
      Call MRes: Maybe resK <- rfRead(#handling: ReqId);
      Call req: reqK <- rfRead(#handling: ReqId);
      LET resp <- STRUCT { "req" ::= #req;
                           "res" ::= #MRes @% "data" };
      If #MRes @% "valid" then (
        LETA _ <- prefetcherCallback (resp : ty ReqRes);
        Write handlingName <- #handling + $1;
        Retv
      );
      Retv.

   Definition TranslatorResponse: Kind := STRUCT_TYPE { "id" :: ReqId; "res" :: resK }.
  
   (* Action the arbiter will call when giving us (the reorderer) the
      response to a prior request *)
   Definition reordererCallback (resp: ty TranslatorResponse): ActionT ty Void :=
    LET idx: ReqId <- #resp @% "id";
    LET res: resK <- #resp @% "res";
    Call rfWrite(STRUCT { "addr" ::= #idx;
                          "data" ::= Valid #res } : WriteRq reqIdSz (Maybe resK));
    Retv.
    
   (* Action the prefetcher will ultimately use to make an order-preserving request for instructions at some address *)
   Definition req (p: ty reqK): ActionT ty Bool :=
     Read giving: ReqId <- givingName;
     Read handling: ReqId <- handlingName;
     LET taggedReq <- STRUCT { "tag" ::= #giving;
                               "req" ::= #p };
     If (#giving + $1) != #handling then ( (* we can give a new reqid without forgetting the next one to service *)
        LETA res: Bool <- memReq (taggedReq);
        If #res then (
            Write givingName: ReqId <- #giving + $1;
            Call rfWrite(STRUCT { "addr" ::= #giving;
                                  "data" ::= Invalid } : WriteRq reqIdSz (Maybe resK));
            Call arfWrite(STRUCT { "addr" ::= #giving;
                                   "data" ::= #p } : WriteRq reqIdSz reqK);
            Retv
            );
        Ret #res
      ) else (
        Ret $$false
      ) as ret;
      Ret #ret.
  End withParams.
End Reorderer.
