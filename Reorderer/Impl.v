Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.Reorderer.Ifc.
Section Reorderer.
  Context `{ReordererParams}.

  Local Definition rfName     := (StdLibKami.Reorderer.Ifc.name ++ ".rfName")%string.
  Local Definition rfRead     := (StdLibKami.Reorderer.Ifc.name ++ ".rfRead")%string.
  Local Definition rfWrite    := (StdLibKami.Reorderer.Ifc.name ++ ".rfWrite")%string.
  Local Definition arfName    := (StdLibKami.Reorderer.Ifc.name ++ ".arfName")%string.
  Local Definition arfRead    := (StdLibKami.Reorderer.Ifc.name ++ ".arfRead")%string.
  Local Definition arfWrite   := (StdLibKami.Reorderer.Ifc.name ++ ".arfWrite")%string.
  Local Definition enqPtr     := (StdLibKami.Reorderer.Ifc.name ++ ".enqPtr")%string.
  Local Definition deqPtr     := (StdLibKami.Reorderer.Ifc.name ++ ".deqPtr")%string.
  Local Definition validArray := (StdLibKami.Reorderer.Ifc.name ++ ".validArray")%string.

  Class ReordererImplParams :=
    {
      logNumReqId: nat;
      lenIsPow2: Nat.pow 2 logNumReqId = numReqId;
    }.

  Section withParams.
    Context `{ReordererImplParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Lemma logNumReqId_reqIdSz: logNumReqId = reqIdSz.
    Proof.
      unfold reqIdSz.
      rewrite <- lenIsPow2.
      rewrite Nat.log2_up_pow2; auto; try Omega.omega.
    Qed.

    Definition castToReqIdSz (t: nat -> Type) (val: t logNumReqId): t reqIdSz :=
      eq_rect logNumReqId t val reqIdSz logNumReqId_reqIdSz.
    
    Definition ReordererPtr := Bit (logNumReqId + 1).
    Section withTy.
      Definition sendReq
                 ty
                 (isError : immResK @# ty -> Bool @# ty)
                 (memReq
                  : ty ReordererArbiterReq ->
                    ActionT ty ReordererImmRes)
                 (req: ty ReordererReq)
        :  ActionT ty Bool
        := System [
             DispString _ "[Reorderer.sendReq]\n"
           ];
           Read enqPFull: ReordererPtr <- enqPtr;
           Read deqPFull: ReordererPtr <- deqPtr;
           Read valids: Array numReqId Bool <- validArray;
           LET enqP: ReordererReqId <- UniBit (TruncLsb _ 1)
                                    (castToReqIdSz (fun n => Expr ty (SyntaxKind (Bit (n + 1)))) #enqPFull);
           LET deqP: ReordererReqId <- UniBit (TruncLsb _ 1)
                                    (castToReqIdSz (fun n => Expr ty (SyntaxKind (Bit (n + 1)))) #deqPFull);
           LET arbiterReq
           :  ReordererArbiterReq
                <- STRUCT {
                  "tag" ::= #enqP;
                  "req" ::= #req @% "paddr" @% "data"
                };
           If (#deqPFull + $(Nat.pow 2 reqIdSz)) != #enqPFull
           then
             If #req @% "paddr" @% "valid"
             then memReq arbiterReq
             else Ret (STRUCT { "ready" ::= $$ true;
                                "info" ::= $$ (getDefaultConst immResK)})
             as res;
             If #res @% "ready"
             then
               Write enqPtr <- #enqPFull + $1;
               LET dataVal : ReordererStorage <- STRUCT { "vaddr" ::= #req @% "vaddr" ;
                                                          "info" ::= #res @% "info" };
               WriteRf arfWrite(#enqP : reqIdSz ; #dataVal : ReordererStorage);
               Write validArray: Array numReqId Bool <- #valids@[#enqP <- (IF #req @% "paddr" @% "valid"
                                                                           then isError (#res @% "info")
                                                                           else $$ true)];
               Retv;
             Ret (#res @% "ready")
           else Ret $$false
           as ret;
           Ret #ret.

      (* Action the arbiter will call when giving us (the reorderer) the
         response to a prior request *)
      Definition reordererCallback ty (resp: ty ReordererArbiterRes): ActionT ty Void :=
        System [
          DispString _ "[Reorderer.reordererCallback]\n"
        ];
        LET idx: ReordererReqId <- #resp @% "tag";
        LET res: mInstK <- #resp @% "resp";
        Read valids: Array numReqId Bool <- validArray;
        Write validArray: Array numReqId Bool <- #valids@[#idx <- $$true];
        WriteRf rfWrite(#idx: reqIdSz ; #res: mInstK);
        System [
          DispString _ "[Reorderer.reordererCallback] stored response:\n";
          DispHex #res;
          DispString _ "\n"
        ];
        Retv.

      (* Conceptual rule *)
      Definition responseToPrefetcherRule
                 (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void)
                 ty
      : ActionT ty Void
        := System [
             DispString _ "[Reorderer.responseToPrefetcher]\n"
           ];
           Read deqPFull: ReordererPtr <- deqPtr;
           Read enqPFull: ReordererPtr <- enqPtr;
           Read valids: Array numReqId Bool <- validArray;
           LET deqP: ReordererReqId
                       <- UniBit (TruncLsb _ 1)
                       (castToReqIdSz (fun n => Expr ty (SyntaxKind (Bit (n + 1)))) #deqPFull);
           ReadRf inst: mInstK <- rfRead(#deqP: ReordererReqId);
           ReadRf vaddrInfo: ReordererStorage <- arfRead(#deqP: ReordererReqId);
           LET resp
           :  ReordererRes
                <- STRUCT {
                  "vaddr" ::= #vaddrInfo @% "vaddr";
                  "info"  ::= #vaddrInfo @% "info";
                  "inst"  ::= #inst
                };
           If (#deqPFull != #enqPFull) && (#valids@[#deqP])
           then
             System [
               DispString _ "[Reorderer.responseToPrefetcher] sending response to prefetcher:";
               DispHex #resp;
               DispString _ "\n"
             ];
             LETA _ <- prefetcherCallback (resp : ty ReordererRes);
             Write deqPtr <- #deqPFull + $1;
             Retv;
           Retv.

    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    
    Definition regs: list RegInitT := makeModule_regs ( Register enqPtr: ReordererPtr <- $ 0 ++
                                                        Register deqPtr: ReordererPtr <- $ 0 ++
                                                        RegisterU validArray: Array numReqId Bool                                                                  ).

    Definition regFiles: list RegFileBase :=
      [ 
        @Build_RegFileBase false 1 rfName
                           (Async [rfRead]) rfWrite (Nat.pow 2 reqIdSz) mInstK (@RFNonFile _ _ None);
          
        @Build_RegFileBase false 1 arfName
                           (Async [arfRead]) arfWrite (Nat.pow 2 reqIdSz) ReordererStorage (@RFNonFile _ _ None)
      ].
    

    Instance implReorderer: Reorderer :=
      {|
        Reorderer.Ifc.regs := regs;
        Reorderer.Ifc.regFiles := regFiles;
        Reorderer.Ifc.responseToPrefetcherRule := responseToPrefetcherRule;
        Reorderer.Ifc.callback := reordererCallback;
        Reorderer.Ifc.sendReq := sendReq
      |}.
  End withParams.
End Reorderer.
