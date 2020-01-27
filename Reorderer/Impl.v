Require Import Kami.All.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.Reorderer.Ifc.
Section Reorderer.
  Context `{ReordererParams}.
  Class ReordererImplParams :=
    {
      (* Methods for interacting with the response buffer (holding Maybe Insts). *)
      rfName: string;
      rfRead: string;
      rfWrite: string;
      (* methods for interacting with the address memory, which keeps
         track of the address each request corresponds to *)
      arfName: string;
      arfRead: string;
      arfWrite: string;

      enqPtr: string;
      deqPtr: string;

      validArray: string;

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
                 (isError : ImmRes @# ty -> Bool @# ty)
                 (memReq
                  : ty ReordererArbiterReq ->
                    ActionT ty ReordererImmRes)
                 (req: ty ReordererReq)
        :  ActionT ty Bool
        := Read enqPFull: ReordererPtr <- enqPtr;
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
                  "req" ::= #req @% "paddr"
                };
           If (#deqPFull + $(Nat.pow 2 reqIdSz)) != #enqPFull
           then
             LETA res <- memReq arbiterReq;
             If #res @% "ready" && (!isError (#res @% "info"))
             then
               Write enqPtr <- #enqPFull + $1;
               Write validArray: Array numReqId Bool <- #valids@[#enqP <- $$false];
               LET dataVal : ReordererStorage <- STRUCT { "vaddr" ::= #req @% "vaddr" ;
                                                          "info" ::= #res @% "info" };
               WriteRf arfWrite(#enqP : reqIdSz ; #dataVal : ReordererStorage);
               Retv;
             Ret (#res @% "ready")
           else Ret $$false
           as ret;
           Ret #ret.

      (* Action the arbiter will call when giving us (the reorderer) the
         response to a prior request *)
      Definition reordererCallback ty (resp: ty ReordererArbiterRes): ActionT ty Void :=
        LET idx: ReordererReqId <- #resp @% "tag";
        LET res: MInst <- #resp @% "resp";
        Read valids: Array numReqId Bool <- validArray;
        Write validArray: Array numReqId Bool <- #valids@[#idx <- $$true];
        WriteRf rfWrite(#idx: reqIdSz ; #res: MInst);
        Retv.

      (* Conceptual rule *)
      Definition responseToPrefetcher
                 (prefetcherCallback: forall {ty}, ty ReordererRes -> ActionT ty Void)
                 ty
      : ActionT ty Void
        := Read deqPFull: ReordererPtr <- deqPtr;
           Read enqPFull: ReordererPtr <- enqPtr;
           Read valids: Array numReqId Bool <- validArray;
           LET deqP: ReordererReqId
                       <- UniBit (TruncLsb _ 1)
                       (castToReqIdSz (fun n => Expr ty (SyntaxKind (Bit (n + 1)))) #deqPFull);
           ReadRf inst: MInst <- rfRead(#deqP: ReordererReqId);
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
                           (Async [rfRead]) rfWrite reqIdSz MInst (@RFNonFile _ _ None);
          
        @Build_RegFileBase false 1 arfName
                           (Async [arfRead]) arfWrite reqIdSz ReordererStorage (@RFNonFile _ _ None)
      ].
    

    Instance implReorderer: Reorderer :=
      {|
        Reorderer.Ifc.regs := regs;
        Reorderer.Ifc.regFiles := regFiles;
        Reorderer.Ifc.responseToPrefetcher := responseToPrefetcher;
        Reorderer.Ifc.callback := reordererCallback;
        Reorderer.Ifc.sendReq := sendReq
      |}.
  End withParams.
End Reorderer.
