(* TODO: LLEE rename to Impl.v *)
Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.Async.
Require Import StdLibKami.Prefetcher.FifoTop.Ifc.

Section AsyncFifoTop.
  Context `{fifoTopParams: FifoTopParams}.
  Class AsyncFifoTopParams :=
    {
      backingFifo: @Fifo PrefetcherFifoEntry;
      outstandingFifo: @Fifo Void;
      topReg: string;
      isCompleting: string;
      sameLen: @Fifo.Ifc.getLen _ backingFifo = @Fifo.Ifc.getLen _ outstandingFifo;
    }.
  
  Section withParams.
    Context `{AsyncFifoTopParams}.
    Local Open Scope kami_expr.
    Local Open Scope kami_action.
    
    Section withTy.
      Context (ty: Kind -> Type).

      (* Completing => Not empty *)
      Definition GetIsCompleting: ActionT ty (Maybe VAddr) :=
        Read completing: Bool <- isCompleting;
        Read top: TopEntry <- topReg;          
        Ret (STRUCT { "valid" ::= #completing;
                      "data" ::= toFullVAddr (#top @% "vaddr" + $1)}: Maybe VAddr @# ty).
  
      Definition ResetCompleting: ActionT ty Void :=
        Write isCompleting: Bool <- $$false;
        Retv.
  
      Local Definition TopIsEmpty: ActionT ty Bool :=
        Read top: TopEntry <- topReg;
        LET upper: Maybe (@CompInst fifoTopParams) <- #top @% "upper";
        Ret !(#upper @% "valid"). (* we maintain the invariant that the upper portion of the top register is valid for any non-empty Fifo *)
    
      Definition isEmpty: ActionT ty Bool :=
        LETA topEmpty: Bool <- TopIsEmpty;
        LETA fifoEmpty: Bool <- (@Fifo.Ifc.isEmpty _ backingFifo ty);
        Ret (#topEmpty && #fifoEmpty).
  
      Definition isFull: ActionT ty Bool :=
        @Fifo.Ifc.isFull _ backingFifo ty.

      Definition isFullOutstanding: ActionT ty Bool :=
        @Fifo.Ifc.isFull _ outstandingFifo ty.

      Definition enqOutstanding: ActionT ty Bool :=
        LET dummy: Void <- $0;
        @Fifo.Ifc.enq _ outstandingFifo ty dummy.

      Definition deqOutstanding: ActionT ty Void :=
        LETA _ <- @Fifo.Ifc.deq _ outstandingFifo ty;
        Retv.
      
      Definition enq (new: ty PrefetcherFifoEntry): ActionT ty Bool := 
        Read top: TopEntry <- topReg;
        Read completing: Maybe VAddr <- isCompleting;
        LETA isFull: Bool <- (@Fifo.Ifc.isFull _ backingFifo _);
        LETA isEmp: Bool <- isEmpty;
        
        LET minst: Maybe Inst <- #new @% "inst";
        LET inst: Inst <- #minst @% "data";
        LET noErr: Bool <- #minst @% "valid";
        LET vaddr <- #new @% "vaddr";
        LET completingAddr: (@VAddr fifoTopParams) <- #completing @% "data";
        LET newCompleting: Maybe VAddr <- (IF  (#completing @% "valid") && toFullVAddr #vaddr == #completingAddr
                                           then Invalid
                                           else #completing);
        LET drop: Bool <- #completing @% "valid" && toFullVAddr #vaddr != #completingAddr;
        If !#drop
        then (
          If !#isEmp
          then (LETA _ <- (@Fifo.Ifc.enq _ backingFifo _) new; Retv)
          else (Write topReg: TopEntry <- (STRUCT { "vaddr" ::= (#vaddr: ShortVAddr @# ty);
                                                    "info"  ::= #new @% "info";
                                                    "noErr" ::= #noErr;
                                                    "upper" ::= (Valid (ZeroExtendTruncMsb CompInstSz #inst): Maybe CompInst @# ty);
                                                    "lower" ::= (Valid (ZeroExtendTruncLsb CompInstSz #inst): Maybe CompInst @# ty) });
                LETA _ <- @Fifo.Ifc.deq _ outstandingFifo _;
                Retv);
          Retv);
        Write isCompleting: Maybe VAddr <- #newCompleting;
        Ret !#isFull.
  
      Definition deq: ActionT ty DeqRes := 
        Read top: TopEntry <- topReg;
        Read completing: Bool <- isCompleting;
        LETA fifoEmpty: Bool <- (@Fifo.Ifc.isEmpty _ backingFifo _);
        LETA ftop: Maybe PrefetcherFifoEntry <- (@Ifc.first _ backingFifo _);

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

        LET retAddr: VAddr <-
          (IF isErr #topInfo || !#topNoErr
           then toFullVAddr #topShortAddr
           else (IF #lowerValid
                 then toFullVAddr #topShortAddr
                 else (IF #upperCompressed
                       then (toFullVAddr #topShortAddr) + $2
                       else (IF #fifoEmpty || #ftopShortAddr != (#topShortAddr + $1)
                             then toFullVAddr (#topShortAddr + $1)
                             else (toFullVAddr #topShortAddr) + $2))));

        LET doComplete <- !#lowerValid && !#upperCompressed && (#fifoEmpty || #ftopShortAddr != (#topShortAddr + $1));

        LET retInst: Inst <-
          (IF #lowerValid
           then #topFull
           else (IF #upperCompressed
                 then #upperFull
                 else #completedInst));

        LET doDeq: Bool <-
          (isErr #topInfo || !#topNoErr) ||
          (#lowerValid && !#lowerCompressed) ||
          (!#lowerValid && !#doComplete);

        If #doDeq || #doComplete
        then (LETA _ <- @Fifo.Ifc.deq _ outstandingFifo _;
              @Fifo.Ifc.deq _ backingFifo _);

        Write isCompleting: Bool <- #doComplete;

        LET newTopEntry: TopEntry <- (IF #doDeq
                                      then STRUCT { "vaddr" ::= #ftopShortAddr ;
                                                    "info"  ::= #ftopInfo ;
                                                    "noErr" ::= #ftopNoErr ;
                                                    "upper" ::= STRUCT { "valid" ::= !#fifoEmpty;
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

        LETA isEmp: Bool <- isEmpty;
        LET retError: DeqError <- (IF #isEmp
                                   then $EmptyError
                                   else (IF #doComplete
                                         then $IncompleteError
                                         else $NoError));
          
        LET ret: DeqRes <- STRUCT { "error" ::= #retError;
                                    "vaddr" ::= #retAddr;
                                    "info"  ::= #topInfo;
                                    "noErr" ::= #topNoErr;
                                    "inst"  ::= #retInst};
        Ret #ret.
  
    End withTy.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.

    Definition regs: list RegInitT := makeModule_regs ( Register topReg: TopEntry <- Default ++
                                                        Register isCompleting: Bool <- Default )
                                      ++ (@Fifo.Ifc.regs _ backingFifo)
                                      ++ (@Fifo.Ifc.regs _ outstandingFifo).

    Definition regFiles := (@Fifo.Ifc.regFiles _ backingFifo)
                           ++ (@Fifo.Ifc.regFiles _ outstandingFifo).
    
    Instance asyncFifoTop: FifoTop.Ifc.FifoTop := 
      {|
        FifoTop.Ifc.regs := regs;
        FifoTop.Ifc.regFiles := regFiles;
        FifoTop.Ifc.getIsCompleting := GetIsCompleting;
        FifoTop.Ifc.resetCompleting := ResetCompleting;
        FifoTop.Ifc.isEmpty := isEmpty;
        FifoTop.Ifc.isFull := isFull;
        FifoTop.Ifc.deq := deq;
        FifoTop.Ifc.enq := enq;
        FifoTop.Ifc.enqOutstanding := enqOutstanding;
        FifoTop.Ifc.isFullOutstanding := isFullOutstanding;
      |}.
  End withParams.
End AsyncFifoTop.
