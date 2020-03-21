Require Import Kami.AllNotations.

Class Params :=
  { name : string;
    size : nat;
    inReqK : Kind;
    vAddrSz : nat;
    compInstSz : nat;
    immResK : Kind;
    finalErrK : Kind;
    isCompressed: forall ty, Bit compInstSz @# ty -> Bool @# ty;
    isImmErr: forall ty, immResK @# ty -> Bool @# ty;
    isFinalErr: forall ty, finalErrK @# ty -> Bool @# ty;
  }.

Section Ifc.
  Context {params: Params}.

  Definition VAddr    := Bit vAddrSz.
  Definition ShortVAddr := Bit (vAddrSz - 2).
  Definition CompInst := Bit compInstSz.
  Definition InstSz   := compInstSz + compInstSz.
  Definition Inst     := Bit InstSz.

  Definition TopEntry: Kind
    := STRUCT_TYPE {
         "vaddr"  :: ShortVAddr;
         "immRes" :: immResK;
         "error"  :: finalErrK;
         "upper"  :: Maybe CompInst;
         "lower"  :: Maybe CompInst
       }.
  
  Definition OutReq := STRUCT_TYPE { "inReq" :: inReqK;
                                     "vaddr" :: VAddr }.

  Definition InRes
    := STRUCT_TYPE {
         "vaddr"  :: VAddr;
         "immRes" :: immResK;
         "error"  :: finalErrK;
         "inst"   :: Inst
       }.

  (* if inst contains a compressed instruction the upper 16 bit contain arbitrary data. *)
  Definition OutRes
    := STRUCT_TYPE {
         "notComplete?" :: Bool;
         "vaddr"        :: VAddr;
         "immRes"       :: immResK;
         "error"        :: finalErrK;
         "compressed?"  :: Bool;
         "errUpper?"    :: Bool;
         "inst"         :: Inst 
       }.

  Record Ifc: Type :=
    {
      regs: list RegInitT;
      regFiles : list RegFileBase;

      isFull: forall {ty}, ActionT ty Bool;
      sendAddr (sendReq: forall ty, ty OutReq -> ActionT ty Bool) ty: ty OutReq -> ActionT ty Bool;
      callback: forall {ty}, ty InRes -> ActionT ty Void;
      deq: forall {ty}, ActionT ty Bool;
      first: forall {ty}, ActionT ty (Maybe OutRes);

      canClear: forall {ty}, ActionT ty Bool;
      clear: forall {ty}, ActionT ty Void;

      notCompleteDeqRule: forall {ty}, ActionT ty Void;
      transferRule: forall {ty}, ActionT ty Void;
    }.
End Ifc.
