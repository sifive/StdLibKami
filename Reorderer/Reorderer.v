Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.

Section Reorderer.
  Context (name: string).
  Context (ty: Kind -> Type).
  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Context (ReqK ResK: Kind).
  Definition ReqRes: Kind := STRUCT_TYPE { "req" :: ReqK;
                                           "res" :: ResK }.

  Context (ReqIdSz: nat).
  Definition ReqId := Bit ReqIdSz.

  (* Methods for interacting with the response buffer (holding Maybe
     Insts). *)
  Context (rfRead rfWrite: string).
  (* methods for interacting with the address memory, which keeps
     track of the address each request corresponds to *)
  Context (arfRead arfWrite: string).

  Definition handlingName := (name ++ "_" ++ "handlingCtr")%string.
  Definition givingName := (name ++ "_" ++ "givingCtr")%string.

  Context (prefetcherCallback: ty ReqRes -> ActionT ty Void).
  Definition ReordererReq := STRUCT_TYPE { "tag" :: ReqId;
                                           "req" :: ReqK }.
  (* The request action assigned to us by the translator *)
  Context (translatorReq: ty ReordererReq -> ActionT ty Bool).
  
  (* Conceptual rule *)
  Definition handle: ActionT ty Void :=
    Read handling: ReqId <- handlingName;
    Call MRes: Maybe ResK <- rfRead(#handling: ReqId);
    Call req: ReqK <- rfRead(#handling: ReqId);
    LET resp <- STRUCT { "req" ::= #req;
                         "res" ::= #MRes @% "data" };
    If #MRes @% "valid" then (
      LETA _ <- prefetcherCallback (resp : ty ReqRes);
      Write handlingName <- #handling + $1;
      Retv
    );
    Retv.

  Definition TranslatorResponse: Kind := STRUCT_TYPE { "id" :: ReqId; "res" :: ResK }.
  
  (* Action the translator will call when giving us (the reorderer) the response to a prior request *)
  Definition reordererCallback (resp: ty TranslatorResponse): ActionT ty Void :=
    (* When a response comes back tagged with a count c, we will write
       at index c into the response buffer Valid(response_data). *)
    LET idx: ReqId <- #resp @% "id";
    LET res: ResK <- #resp @% "res";
    Call rfWrite(STRUCT { "addr" ::= #idx;
                          "data" ::= Valid #res } : WriteRq ReqIdSz (Maybe ResK));
    Retv.
    
  (* Action the prefetcher will ultimately use to make an order-preserving request for instructions at some address *)
  Definition req (p: ty ReqK): ActionT ty Bool :=
    Read giving: ReqId <- givingName;
    Read handling: ReqId <- handlingName;
    LET taggedReq <- STRUCT { "tag" ::= #giving;
                          "req" ::= #p };
    If (#giving + $1) != #handling then ( (* we can give a new reqid without forgetting the next one to service *)

        LETA res: Bool <- translatorReq (taggedReq);
        If #res then (
            Write givingName: ReqId <- #giving + $1;
            Call rfWrite(STRUCT { "addr" ::= #giving;
                                  "data" ::= Invalid } : WriteRq ReqIdSz (Maybe ResK));
            Call arfWrite(STRUCT { "addr" ::= #giving;
                                   "data" ::= #p } : WriteRq ReqIdSz ReqK);
            Retv
            );
        Ret #res
      ) else (
        Ret $$false
      ) as ret;
      Ret #ret.
End Reorderer.
