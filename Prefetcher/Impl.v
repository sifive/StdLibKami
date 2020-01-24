Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.Ifc.

Section Prefetch.
  Context `{prefetcherParams: PrefetcherParams}.
  Context (fifo: Fifo.Ifc.Fifo PrefetcherFifoEntry).
  Context (outstanding: Fifo.Ifc.Fifo Void).

  Class PrefetcherImplParams :=
    { topReg : string ;
      lenMatches : @Fifo.Ifc.getLen _ fifo = @Fifo.Ifc.getLen _ outstanding }.

  Context (prefetcherImplParams: PrefetcherImplParams).

  Local Definition PAddr    := Bit PAddrSz.
  Local Definition VAddr    := Bit VAddrSz.
  Local Definition CompInst := Bit CompInstSz.
  Local Definition InstSz   := CompInstSz + CompInstSz.
  Local Definition Inst     := Bit InstSz.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition isFull ty: ActionT ty Bool :=
    @Fifo.Ifc.isFull _ outstanding _.

  Definition clearTop ty: ActionT ty Void :=
    Write topReg: TopEntry <-
      STRUCT {
        "vaddr" ::= $0;
        "info"  ::= $$(getDefaultConst ImmRes);
        "noErr" ::= $$false;
        "upper" ::= (Invalid: Maybe CompInst @# ty);
        "lower" ::= (Invalid: Maybe CompInst @# ty)};
      Retv.

  Definition isNotComplete ty: ActionT ty Bool :=
    Read top: TopEntry <- topReg;
    LETA ftop: Maybe PrefetcherFifoEntry <- @Fifo.Ifc.first _ fifo _;
    Ret ((#top @% "upper" @% "valid")
           && !(#top @% "lower" @% "valid")
           && !(isCompressed (#top @% "upper" @% "data"))
           && (!(#ftop @%"valid") || ((#top @% "vaddr" + $1) != #ftop @% "data" @% "vaddr"))).

  Definition notCompleteDeq ty: ActionT ty Void :=
    LETA notComplete <- isNotComplete _;
    Read top: TopEntry <- topReg;
    LETA ftop: Maybe PrefetcherFifoEntry <- @Fifo.Ifc.first _ fifo _;
    If #notComplete && #ftop @% "valid" && (#top @% "vaddr" + $1) != #ftop @% "data" @% "vaddr"
    then (
      LETA _ <- @Fifo.Ifc.deq _ fifo _;
      @Fifo.Ifc.deq _ outstanding _
    );
    Retv.       

  Definition transfer ty: ActionT ty Void :=
    Read top: TopEntry <- topReg;
    LETA isEmp: Bool <- @Fifo.Ifc.isEmpty _ fifo _;
    If !(#top @% "upper" @% "valid") && !#isEmp
    then (
      LETA deqValM: Maybe PrefetcherFifoEntry <- @Fifo.Ifc.deq _ fifo _;
      LETA _ <- @Fifo.Ifc.deq _ outstanding _;
      LET deqVal: PrefetcherFifoEntry <- #deqValM @% "data";    
      Write topReg: TopEntry <-
        STRUCT {
          "vaddr" ::= #deqVal @% "vaddr";
          "info"  ::= #deqVal @% "info";
          "noErr" ::= #deqVal @% "inst" @% "valid";
          "upper" ::= Valid (UniBit (TruncMsb _ _) (#deqVal @% "inst" @% "data"));
          "lower" ::= Valid (UniBit (TruncLsb _ _) (#deqVal @% "inst" @% "data"))};
      Retv );
    Retv.

  Definition memCallback ty (reordererRes: ty PrefetcherRes)
    :  ActionT ty Void
    := LET entryData
         :  PrefetcherFifoEntry
         <- STRUCT {
              "vaddr" ::= (toShortVAddr (#reordererRes @% "vaddr" : VAddr @# ty));
              "info"  ::= #reordererRes @% "info";
              "inst"  ::= (#reordererRes @% "inst": Maybe Inst @# ty)
            };
       LETA _ <- @Fifo.Ifc.enq _ fifo _ entryData;
       Retv.

  Definition doPrefetch ty (memReq : ty PrefetcherReq -> ActionT ty Bool) (prefetcherReq: ty PrefetcherReq)
    : ActionT ty Bool
    := LETA retval <- memReq prefetcherReq;
       LET dummy: Void <- $$(getDefaultConst Void);
       LETA _ <- @Fifo.Ifc.enq _ outstanding _ dummy;
       Ret #retval.

  Definition fetchInstruction ty : ActionT ty (Maybe DeqRes) :=
    Read top: TopEntry <- topReg;
    LETA ftop: Maybe PrefetcherFifoEntry <- (@Fifo.Ifc.first _ fifo _);

    LET topInfo: ImmRes <- #top @% "info";
    LET topNoErr: Bool <- #top @% "noErr";
    LET topShortAddr: ShortVAddr <- #top @% "vaddr";
    LET lower: Maybe CompInst <- #top @% "lower";
    LET lowerValid: Bool <- #lower @% "valid";
    LET lowerInst: CompInst <- #lower @% "data";
    LET lowerCompressed: Bool <- isCompressed #lowerInst;
    LET upper: Maybe CompInst <- #top @% "upper";
    LET upperValid: Bool <- #upper @% "valid";
    LET upperInst: CompInst <- #upper @% "data";
    LET upperCompressed: Bool <- isCompressed #upperInst;
    LET lowerFull: Inst <- (ZeroExtend _ #lowerInst: Inst @# ty);
    LET upperFull: Inst <- (ZeroExtend _ #upperInst: Inst @# ty);
    LET topFull: Inst <- {< #upperInst, #lowerInst >};

    LET ftopAddrInst: PrefetcherFifoEntry <- #ftop @% "data";
    LET ftopShortAddr: ShortVAddr <- #ftopAddrInst @% "vaddr";

    LET ftopMInst: Maybe Inst <- #ftopAddrInst @% "inst";
    LET ftopInfo: ImmRes <- #ftopAddrInst @% "info";
    LET ftopNoErr: Bool <- #ftopMInst @% "valid";
    LET ftopInst : Inst <- #ftopMInst @% "data";
    LET ftopUpperInst: CompInst <- ZeroExtendTruncMsb _ #ftopInst;
    LET ftopLowerInst: CompInst <- ZeroExtendTruncLsb _ #ftopInst;

    LET completedInst: Inst <- {< #ftopLowerInst, #upperInst >};

    LETA notComplete : Bool <- isNotComplete _;

    LET retAddr: VAddr <-
      (IF isErr #topInfo || !#topNoErr
       then toFullVAddr #topShortAddr
       else (IF #lowerValid
             then toFullVAddr #topShortAddr
             else (IF #upperCompressed
                   then (toFullVAddr #topShortAddr) + $2
                   else (IF #notComplete
                         then toFullVAddr (#topShortAddr + $1)
                         else (toFullVAddr #topShortAddr) + $2))));

    LET retInst: Inst <-
      (IF #lowerValid
       then #topFull
       else (IF #upperCompressed
             then #upperFull
             else #completedInst));

    LET doDeq: Bool <-
      #upperValid &&
      ((isErr #topInfo || !#topNoErr) ||
       (#lowerValid && !#lowerCompressed) ||
       (!#lowerValid && !#notComplete));

    If #doDeq
    then (LETA _ <- @Fifo.Ifc.deq _ fifo _;
          @Fifo.Ifc.deq _ outstanding _);

    LET newTopEntry: TopEntry <- (IF #doDeq
                                  then STRUCT { "vaddr" ::= #ftopShortAddr ;
                                                "info"  ::= #ftopInfo ;
                                                "noErr" ::= #ftopNoErr ;
                                                "upper" ::= STRUCT { "valid" ::= !(#ftop @% "valid");
                                                                     "data"  ::= #ftopUpperInst } ;
                                                "lower" ::= STRUCT { "valid" ::= (IF #lowerValid
                                                                                  then $$true
                                                                                  else (IF #upperCompressed
                                                                                        then $$true
                                                                                        else $$false));
                                                                     "data"  ::= #ftopLowerInst } }
                                  else STRUCT { "vaddr" ::= #topShortAddr ;
                                                "info"  ::= #topInfo ;
                                                "noErr" ::= #topNoErr ;
                                                "upper" ::= STRUCT { "valid" ::= #upperValid ;
                                                                     "data"  ::= #upperInst } ;
                                                "lower" ::= STRUCT { "valid" ::= $$false ;
                                                                     "data"  ::= #lowerInst } });

    Write topReg: TopEntry <- #newTopEntry;

    LET ret: DeqRes <- STRUCT { "vaddr" ::= #retAddr;
                                "info"  ::= #topInfo;
                                "noErr" ::= #topNoErr;
                                "inst"  ::= #retInst};
    Ret (STRUCT {
           "valid" ::= #upperValid;
           "data"  ::=  #ret }: Maybe DeqRes @# ty).

    
  Open Scope kami_scope.

  Definition regs
    := (makeModule_regs
         (Register topReg : TopEntry <- getDefaultConst TopEntry)) ++
       (@Fifo.Ifc.regs _ fifo ++
        @Fifo.Ifc.regs _ outstanding).

  Close Scope kami_scope.

  Definition regFiles := @Fifo.Ifc.regFiles _ fifo ++ @Fifo.Ifc.regFiles _ outstanding.

  Instance prefetcher: Prefetcher := {| Prefetcher.Ifc.regs := regs;
                                        Prefetcher.Ifc.regFiles := regFiles;
                                        Prefetcher.Ifc.isFull := isFull;
                                        Prefetcher.Ifc.doPrefetch := doPrefetch;
                                        Prefetcher.Ifc.memCallback := memCallback;
                                        Prefetcher.Ifc.fetchInstruction := fetchInstruction;
                                        Prefetcher.Ifc.isNotComplete := isNotComplete;
                                        Prefetcher.Ifc.clearTop := clearTop;
                                        Prefetcher.Ifc.notCompleteDeq := notCompleteDeq;
                                        Prefetcher.Ifc.transfer := transfer; |}.
End Prefetch.
