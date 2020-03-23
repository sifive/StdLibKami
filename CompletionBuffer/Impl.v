Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.FreeList.Ifc.
Require Import StdLibKami.CompletionBuffer.Ifc.

Section Impl.
  Context {ifcParams: Ifc.Params}.

  Class Params := { storeArray: @RegArray.Ifc.Ifc {| RegArray.Ifc.name := name ++ ".storeArray";
                                                     RegArray.Ifc.k := Store;
                                                     RegArray.Ifc.size := size;
                                                     RegArray.Ifc.init := None |} ;
                    resArray: @RegArray.Ifc.Ifc {| RegArray.Ifc.name := name ++ ".resArray";
                                                   RegArray.Ifc.k := resK;
                                                   RegArray.Ifc.size := size;
                                                   RegArray.Ifc.init := None |};
                    freeList: @FreeList.Ifc.Ifc {| FreeList.Ifc.name := name ++ ".freeList";
                                                   FreeList.Ifc.size := size |} }.

  Context {params: Params}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition lgSize := Nat.log2_up size.
  Local Definition Tag := Bit lgSize.

  Local Definition deqPtr := (name ++ ".deqPtr")%string.
  Local Definition enqPtr := (name ++ ".enqPtr")%string.
  Local Definition completedArray := (name ++ ".completedArray")%string.

  Local Definition Ptr := Bit (lgSize + 1).
  
  Local Definition sendReq
        (memReq : forall ty, ty OutReq -> ActionT ty (Maybe immResK))
        ty
        (req: ty inReqK)
    :  ActionT ty Bool
    := Read enqPFull: Ptr <- enqPtr;
       Read deqPFull: Ptr <- deqPtr;
       Read compds: Array size Bool <- completedArray;

       LET enqP: Tag <- UniBit (TruncLsb _ 1) #enqPFull;
       LET deqP: Tag <- UniBit (TruncLsb _ 1) #deqPFull;
       LET outReq
       :  OutReq
            <- STRUCT {
                   "tag"    ::= #enqP;
                   "outReq" ::= inReqToOutReq #req };
       If (#deqPFull + $(Nat.pow 2 lgSize)) != #enqPFull
       then
         If isSend #req
         then memReq _ outReq
         else Ret (STRUCT { "valid" ::= $$true;
                            "data"  ::= $$(getDefaultConst immResK)})
         as res;
         If #res @% "valid"
         then
           Write enqPtr <- #enqPFull + $1;
           LET storeVal : Store <- STRUCT { "storeReq" ::= inReqToStoreReq #req ;
                                            "immRes"   ::= #res @% "data" };
           LET writeRq <- STRUCT { "addr" ::= #enqP;
                                   "data" ::= #storeVal };
           LETA _ <- write storeArray _ writeRq;
           LET isComplete
             :  Bool
             <- (IF isSend #req
                 then isError (#res @% "data")
                 else $$ true);
           Write completedArray: Array size Bool <- #compds@[#enqP <- #isComplete];
           Retv;
         Ret (#res @% "valid")
       else Ret $$false
       as ret;
       Ret #ret.

  Local Definition callback ty (res: ty InRes): ActionT ty Void :=
    LET idx: Tag <- #res @% "tag";
    Read compds: Array size Bool <- completedArray;
    Write completedArray: Array size Bool <- #compds@[#idx <- $$true];
    LET writeRq <- STRUCT { "addr" ::= #idx;
                            "data" ::= #res @% "res" };
    LETA _ <- write resArray _ writeRq;
    Retv.

  (* Conceptual rule *)
  Local Definition callbackRule
        (callback: forall {ty}, ty OutRes -> ActionT ty Void)
        ty
  : ActionT ty Void
    := Read deqPFull: Ptr <- deqPtr;
       Read enqPFull: Ptr <- enqPtr;
       Read compds: Array size Bool <- completedArray;
       LET deqP: Tag <- UniBit (TruncLsb _ 1) #deqPFull;
       LETA resVal: resK <- read resArray _ deqP;
       LETA storeVal: Store <- read storeArray _ deqP;
       LET res
       :  OutRes
          <- STRUCT {
                 "storeReq" ::= #storeVal @% "storeReq" ;
                 "immRes"   ::= #storeVal @% "immRes" ;
                 "res"      ::= #resVal
               };
       If (#deqPFull != #enqPFull) && (#compds@[#deqP])
       then
         LETA _ <- callback (res : ty OutRes);
         Write deqPtr <- #deqPFull + $1;
         Retv;
       Retv.

  Open Scope kami_scope.
  Open Scope kami_expr_scope.

  Local Definition regs : list RegInitT
    := makeModule_regs (
         Register enqPtr: Ptr <- $ 0 ++
         Register deqPtr: Ptr <- $ 0 ++
         Register completedArray: Array size Bool <- Default) ++
       RegArray.Ifc.regs storeArray ++
       RegArray.Ifc.regs resArray ++
       FreeList.Ifc.regs freeList.

  Local Definition regFiles :=
    RegArray.Ifc.regFiles storeArray ++
    RegArray.Ifc.regFiles resArray ++
    FreeList.Ifc.regFiles freeList.

  Definition impl: Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := regFiles;
      Ifc.sendReq := sendReq;
      Ifc.callbackRule := callbackRule;
      Ifc.callback := callback;
    |}.
End Impl.
