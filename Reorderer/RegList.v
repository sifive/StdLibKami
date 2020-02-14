Require Import Kami.All.
Require Import Kami.Utila.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.Reorderer.Ifc.
Section Reorderer.
  Context `{ReordererParams}.

  Local Definition rfName     := (StdLibKami.Reorderer.Ifc.name ++ ".rf")%string.
  Local Definition arfName    := (StdLibKami.Reorderer.Ifc.name ++ ".arf")%string.
  Local Definition enqPtr     := (StdLibKami.Reorderer.Ifc.name ++ ".enqPtr")%string.
  Local Definition deqPtr     := (StdLibKami.Reorderer.Ifc.name ++ ".deqPtr")%string.
  Local Definition validArray := (StdLibKami.Reorderer.Ifc.name ++ ".validArray")%string.

  Local Definition rfRegNames
    :  list string
    := map
         (fun i : nat => (rfName ++ "_" ++ natToHexStr i)%string)
         (seq 0 numReqId).

  Local Definition arfRegNames
    :  list string
    := map
         (fun i : nat => (arfName ++ "_" ++ natToHexStr i)%string)
         (seq 0 numReqId).

  Local Definition rfRegs
    :  list ModuleElt
    := map
         (fun name : string
           => MERegister (name, existT RegInitValT (SyntaxKind mInstK) None))
         rfRegNames.

  Local Definition arfRegs
    :  list ModuleElt
    := map
         (fun name : string
           => MERegister (name, existT RegInitValT (SyntaxKind ReordererStorage) None))
         arfRegNames.
    
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
                    ActionT ty (Maybe immResK))
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
                  "tag"   ::= #enqP;
                  "mode"  ::= #req @% "mode";
                  "paddr" ::= #req @% "paddr" @% "data"
                };
           If (#deqPFull + $(Nat.pow 2 reqIdSz)) != #enqPFull
           then
             System [
               DispString _ "[Reorderer.sendReq] enqP: ";
               DispHex #enqP;
               DispString _ "\n";
               DispString _ "[Reorderer.sendReq] forwarding request to Arbiter: ";
               DispHex #arbiterReq;
               DispString _ "\n"
             ]; 

             If #req @% "paddr" @% "valid"
             then memReq arbiterReq
             else Ret (STRUCT { "valid" ::= $$true;
                                "data"  ::= $$(getDefaultConst immResK)})
             as res;
             If #res @% "valid"
             then
               Write enqPtr <- #enqPFull + $1;
               LET dataVal : ReordererStorage <- STRUCT { "vaddr" ::= #req @% "vaddr" ;
                                                          "info" ::= #res @% "data" };
               LETA _ <- writeReg arfRegNames numReqId #enqP #dataVal;
               LET isComplete
                 :  Bool
                 <- IF #req @% "paddr" @% "valid"
                      then isError (#res @% "data")
                      else $$ true;
               Write validArray: Array numReqId Bool <- #valids@[#enqP <- #isComplete];
               System [
                 DispString _ "[Reorderer.sendReq] stored request in enqP: ";
                 DispHex #enqP;
                 DispString _ "\n";
                 DispString _ "[Reorderer.sendReq] stored request in deqP: ";
                 DispHex #deqP;
                 DispString _ "\n";
                 DispString _ "[Reorderer.sendReq] request accepted. request complete?: ";
                 DispHex #isComplete;
                 DispString _ "\n";
                 DispString _ "[Reorderer.sendReq] valids: ";
                 DispBinary (pack #valids);
                 DispString _ "\n";
                 DispString _ "[Reorderer.sendReq] new valids: ";
                 DispBinary (pack (#valids@[#enqP <- #isComplete]));
                 DispString _ "\n"
               ]; 
               Retv;
             Ret (#res @% "valid")
           else Ret $$false
           as ret;
           Ret #ret.

      (* Action the arbiter will call when giving us (the reorderer) the
         response to a prior request *)
      Definition reordererCallback ty (resp: ty ReordererArbiterRes): ActionT ty Void :=
        System [
          DispString _ "[Reorderer.reordererCallback] resp: ";
          DispHex #resp;
          DispString _ "\n"
        ];
        LET idx: ReordererReqId <- #resp @% "tag";
        LET res: mInstK <- #resp @% "resp";
        Read valids: Array numReqId Bool <- validArray;
        Write validArray: Array numReqId Bool <- #valids@[#idx <- $$true]; (* <==== IDX is wrong *)
        LETA _ <- writeReg rfRegNames numReqId #idx #res;
        System [
          DispString _ "[Reorderer.reordererCallback] stored response:\n";
          DispHex #res;
          DispString _ "\n";
          DispString _ "[Reorderer.reordererCallback] idx:\n";
          DispHex #idx;
          DispString _ "\n";
          DispString _ "[Reorderer.reordererCallback] valids:\n";
          DispBinary (pack #valids);
          DispString _ "\n";
          DispString _ "[Reorderer.reordererCallback] next valids:\n";
          DispBinary (pack (#valids@[#idx <- $$true]));
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
           LETA inst
             :  mInstK
             <- readReg rfRegNames numReqId #deqP mInstK;
           LETA vaddrInfo
             :  ReordererStorage
             <- readReg arfRegNames numReqId #deqP ReordererStorage;
           LET resp
           :  ReordererRes
                <- STRUCT {
                  "vaddr" ::= #vaddrInfo @% "vaddr";
                  "info"  ::= #vaddrInfo @% "info";
                  "inst"  ::= #inst
                };
           System [
             DispString _ "[Reorderer.responseToPrefetcher] deqP: ";
             DispHex #deqP;
             DispString _ "\n";
             DispString _ "[Reorderer.responseToPrefetcher] deqPFull: ";
             DispHex #deqPFull;
             DispString _ "\n";
             DispString _ "[Reorderer.responseToPrefetcher] enqPFull: ";
             DispHex #enqPFull;
             DispString _ "\n";
             DispString _ "[Reorderer.responseToPrefetcher] valids: ";
             DispBinary (pack #valids);
             DispString _ "\n";
             DispString _ "[Reorderer.responseToPrefetcher] valids entry: ";
             DispBinary (#valids@[#deqP]);
             DispString _ "\n"
           ];
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

    Local Definition regs : list RegInitT
      := makeModule_regs (
           Register enqPtr: ReordererPtr <- $ 0 ++
           Register deqPtr: ReordererPtr <- $ 0 ++
           Register validArray: Array numReqId Bool <- getDefaultConst (Array numReqId Bool) ++
           rfRegs ++
           arfRegs).

    Instance implReorderer: Reorderer :=
      {|
        Reorderer.Ifc.regs := regs;
        Reorderer.Ifc.regFiles := [];
        Reorderer.Ifc.responseToPrefetcherRule := responseToPrefetcherRule;
        Reorderer.Ifc.callback := reordererCallback;
        Reorderer.Ifc.sendReq := sendReq
      |}.
  End withParams.
End Reorderer.
