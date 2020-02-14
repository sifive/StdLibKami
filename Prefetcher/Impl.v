Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Prefetcher.Ifc.

Section Prefetch.
  Context `{prefetcherParams: PrefetcherParams}.
  Instance fifoParams
    :  StdLibKami.Fifo.Ifc.FifoParams
    := {|
         StdLibKami.Fifo.Ifc.name := (StdLibKami.Prefetcher.Ifc.name ++ ".fifo")%string;
         StdLibKami.Fifo.Ifc.k    := PrefetcherFifoEntry;
       |}.

  Instance outstandingFifoParams
    :  StdLibKami.Fifo.Ifc.FifoParams
    := {|
         StdLibKami.Fifo.Ifc.name := (StdLibKami.Prefetcher.Ifc.name ++ ".outstandingFifo")%string;
         StdLibKami.Fifo.Ifc.k    := Void;
       |}.

  Context (fifo: Fifo.Ifc.Fifo fifoParams).
  Context (outstanding: Fifo.Ifc.Fifo outstandingFifoParams).

  Class PrefetcherImplParams :=
    { topReg : string ;
      lenMatches : @Fifo.Ifc.getLen _ fifo = @Fifo.Ifc.getLen _ outstanding }.

  Context (prefetcherImplParams: PrefetcherImplParams).

  Local Definition PAddr    := Bit pAddrSz.
  Local Definition VAddr    := Bit vAddrSz.
  Local Definition CompInst := Bit compInstSz.
  Local Definition InstSz   := compInstSz + compInstSz.
  Local Definition Inst     := Bit InstSz.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Definition isFull ty: ActionT ty Bool :=
    System [
      DispString _ "[Prefetcher.isFull]\n"
    ];
    @Fifo.Ifc.isFull _ outstanding _.

  Definition clearTop ty: ActionT ty Void :=
    System [
      DispString _ "[Prefetcher.clearTop]\n"
    ];
    Write topReg: TopEntry <-
      STRUCT {
        "vaddr" ::= $0;
        "info"  ::= $$(getDefaultConst immResK);
        "noErr" ::= $$false;
        "upper" ::= (Invalid: Maybe CompInst @# ty);
        "lower" ::= (Invalid: Maybe CompInst @# ty)};
      Retv.

  Definition isNotComplete
    ty
    (top : TopEntry @# ty)
    (ftop : Maybe PrefetcherFifoEntry @# ty)
    : ActionT ty Bool :=
    (* Read top: TopEntry <- topReg; *)
    (* LETA ftop: Maybe PrefetcherFifoEntry <- @Fifo.Ifc.first _ fifo _; *)
    System [
      DispString _ "[Prefetcher.isNotComplete]\n"
    ];
    Ret ((top @% "upper" @% "valid")
           && !(top @% "lower" @% "valid")
           && !(isCompressed (top @% "upper" @% "data"))
           && (!(ftop @%"valid") || ((top @% "vaddr" + $1) != ftop @% "data" @% "vaddr"))).

  Definition notCompleteDeqRule ty: ActionT ty Void :=
    System [
      DispString _ "[Prefetcher.notCompleteDeq]\n"
    ];
    Read top: TopEntry <- topReg;
    LETA ftop: Maybe PrefetcherFifoEntry <- @Fifo.Ifc.first _ fifo _;
    LETA notComplete <- isNotComplete #top #ftop;
    If #notComplete && #ftop @% "valid" && (#top @% "vaddr" + $1) != #ftop @% "data" @% "vaddr"
    then (
      LETA _ <- @Fifo.Ifc.deq _ fifo _;
      @Fifo.Ifc.deq _ outstanding _
    );
    Retv.       

  Definition transferRule ty: ActionT ty Void :=
    System [
      DispString _ "[Prefetcher.transfer]\n"
    ];
    Read top: TopEntry <- topReg;
    LETA isEmp: Bool <- @Fifo.Ifc.isEmpty _ fifo _;
    System [
      DispString _ "[Prefetcher.transfer] top: ";
      DispHex #top;
      DispString _ "\n";
      DispString _ "[Prefetcher.transfer] is empty: ";
      DispHex #isEmp;
      DispString _ "\n"
    ];
    If !(#top @% "upper" @% "valid") && !#isEmp
    then (
      LETA deqValM: Maybe PrefetcherFifoEntry <- @Fifo.Ifc.deq _ fifo _;
      LETA _ <- @Fifo.Ifc.deq _ outstanding _;
      LET deqVal: PrefetcherFifoEntry <- #deqValM @% "data";    
      LET topEntry
        :  TopEntry
        <- STRUCT {
             "vaddr" ::= #deqVal @% "vaddr";
             "info"  ::= #deqVal @% "info";
             "noErr" ::= #deqVal @% "inst" @% "valid";
             "upper" ::= Valid (UniBit (TruncMsb _ _) (#deqVal @% "inst" @% "data"));
             "lower" ::= Valid (UniBit (TruncLsb _ _) (#deqVal @% "inst" @% "data"))};
      System [
        DispString _ "[Prefetcher.notCompleteDeq] wrote to topReg topEntry: ";
        DispHex #topEntry;
        DispString _ "\n"
      ];
      Write topReg: TopEntry <- #topEntry;
      Retv );
    Retv.

  Definition memCallback ty (reordererRes: ty PrefetcherRes)
    :  ActionT ty Void
    := System [
         DispString _ "[Prefetcher.memCallback] reordererRes: \n";
         DispHex #reordererRes;
         DispString _ "\n"
       ];
       LET entryData
         :  PrefetcherFifoEntry
         <- STRUCT {
              "vaddr" ::= (toShortVAddr (#reordererRes @% "vaddr" : VAddr @# ty));
              "info"  ::= #reordererRes @% "info";
              "inst"  ::= (#reordererRes @% "inst": Maybe Inst @# ty)
            };
       System [
         DispString _ "[Prefetcher.memCallback] write to the prefetcher fifo: \n";
         DispHex #entryData;
         DispString _ "\n"
       ];
       LETA _ <- @Fifo.Ifc.enq _ fifo _ entryData;
       Retv.

  Definition doPrefetch ty (memReq : ty PrefetcherReq -> ActionT ty Bool) (prefetcherReq: ty PrefetcherReq)
    : ActionT ty Bool
    := System [
         DispString _ "[Prefetcher.doPrefetch]\n"
       ];
       LETA retval <- memReq prefetcherReq;
       LET dummy: Void <- $$(getDefaultConst Void);
       LETA _ <- @Fifo.Ifc.enq _ outstanding _ dummy;
(*
       System [
         DispString _ "[Prefetcher.doPrefetch] done\n"
       ];
*)
       Ret #retval.

  Definition fetchInstruction ty : ActionT ty (Maybe DeqRes) :=
    System [
      DispString _ "[Prefetcher.fetchInstruction]\n"
    ];
    Read top: TopEntry <- topReg;
    System [
      DispString _ "[Prefetcher.fetchInstruction] top:\n";
      DispHex #top;
      DispString _ "\n"
    ];
    LETA ftop: Maybe PrefetcherFifoEntry <- (@Fifo.Ifc.first _ fifo _);
    System [
      DispString _ "[Prefetcher.fetchInstruction] ftop:\n";
      DispHex #ftop;
      DispString _ "\n"
    ];
    LET topInfo: immResK <- #top @% "info";
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
    LET ftopInfo: immResK <- #ftopAddrInst @% "info";
    LET ftopNoErr: Bool <- #ftopMInst @% "valid";
    LET ftopInst : Inst <- #ftopMInst @% "data";
    LET ftopUpperInst: CompInst <- ZeroExtendTruncMsb _ #ftopInst;
    LET ftopLowerInst: CompInst <- ZeroExtendTruncLsb _ #ftopInst;

    LET completedInst: Inst <- {< #ftopLowerInst, #upperInst >};

    LETA notComplete : Bool <- isNotComplete #top #ftop;
    System [
      DispString _ "[Prefetcher.fetchInstruction] not complete?:\n";
      DispHex #notComplete;
      DispString _ "\n"
    ];
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

    System [
      DispString _ "[Prefetcher.fetchInstruction] top addr: ";
      DispHex #topShortAddr;
      DispString _ "\n"
    ];

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

    System [
      DispString _ "[Prefetcher.fetchInstruction] doDeq?:\n";
      DispHex #doDeq;
      DispString _ "\n"
    ];

    If #doDeq
    then (LETA _ <- @Fifo.Ifc.deq _ fifo _;
          @Fifo.Ifc.deq _ outstanding _);

    LET newTopEntry: TopEntry <- (IF #doDeq
                                  then STRUCT { "vaddr" ::= #ftopShortAddr ;
                                                "info"  ::= #ftopInfo ;
                                                "noErr" ::= #ftopNoErr ;
                                                "upper" ::= STRUCT { "valid" ::= #ftop @% "valid";
                                                                     "data"  ::= #ftopUpperInst } ;
                                                "lower" ::= STRUCT { "valid" ::= (IF #lowerValid
                                                                                  then #ftop @% "valid"
                                                                                  else (IF #upperCompressed
                                                                                        then #ftop @% "valid"
                                                                                        else $$false));
                                                                     "data"  ::= #ftopLowerInst } }
                                  else STRUCT { "vaddr" ::= #topShortAddr ;
                                                "info"  ::= #topInfo ;
                                                "noErr" ::= #topNoErr ;
                                                "upper" ::= STRUCT { "valid" ::= #upperValid ;
                                                                     "data"  ::= #upperInst } ;
                                                "lower" ::= STRUCT { "valid" ::= $$false ;
                                                                     "data"  ::= #lowerInst } });

    System [
      DispString _ "[Prefetcher.fetchInstruction] new top entry:\n";
      DispHex #newTopEntry;
      DispString _ "\n"
    ];

    Write topReg: TopEntry <- #newTopEntry;

    LET straddle: Bool <- (IF #lowerValid
                           then $$ false
                           else (IF #upperCompressed
                                 then $$ false
                                 else $$ true));

    LET upperOnly: Bool <- (IF #lowerValid
                            then $$ false
                            else (IF #upperCompressed
                                  then $$ true
                                  else $$ false));
    
    LET isErrUpper: Bool <- (IF #straddle
                             then (IF #topNoErr && !(isErr #topInfo)
                                   then $$ true
                                   else $$ false)
                             else $$false);

    LET ret: DeqRes <- STRUCT { "notComplete" ::= #notComplete;
                                "vaddr" ::= #retAddr;
                                "info"  ::= (IF #isErrUpper then #ftopInfo else #topInfo);
                                "noErr" ::= (IF #isErrUpper then #ftopNoErr else #topNoErr);
                                "compressed?" ::= isCompressed (UniBit (TruncLsb compInstSz compInstSz) #retInst);
                                "errUpper?" ::= #isErrUpper;
                                "inst"  ::= #retInst};

    System [
      DispString _ "[Prefetcher.fetchInstruction] deq result:\n";
      DispHex #ret;
      DispString _ "\n"
    ];

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
                                        Prefetcher.Ifc.clearTop := clearTop;
                                        Prefetcher.Ifc.notCompleteDeqRule := notCompleteDeqRule;
                                        Prefetcher.Ifc.transferRule := transferRule; |}.
End Prefetch.
