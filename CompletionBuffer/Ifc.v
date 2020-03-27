Require Import Kami.AllNotations.

Section Ifc.
  Class Params :=
    { name: string;
      size: nat;
      inReqK: Kind;
      outReqK: Kind;
      storeReqK: Kind;
      immResK: Kind;
      inResK: Kind;
      outResK: Kind;
      inReqToOutReq: forall {ty}, inReqK @# ty -> outReqK @# ty;
      inReqToStoreReq: forall {ty}, inReqK @# ty -> storeReqK @# ty;
      isError: forall {ty}, immResK @# ty -> Bool @# ty;
      isSend: forall {ty}, inReqK @# ty -> Bool @# ty;
      inToOutRes: forall {ty}, inResK @# ty -> storeReqK @# ty -> outResK @# ty;
    }.
  
  Context {params: Params}.

  Definition OutReq := STRUCT_TYPE {
                           "tag"    :: Bit (Nat.log2_up size) ;
                           "outReq" :: outReqK
                         }.

  Definition InRes := STRUCT_TYPE {
                          "tag" :: Bit (Nat.log2_up size) ;
                          "res" :: inResK
                        }.

  Definition OutRes := STRUCT_TYPE {
                           "storeReq" :: storeReqK ;
                           "immRes"   :: immResK ;
                           "res"      :: outResK
                         }.

  Definition Store := STRUCT_TYPE {
                          "storeReq" :: storeReqK ;
                          "immRes"   :: immResK
                        }.

  Record Ifc: Type :=
    {
      regs: list RegInitT;
      regFiles: list RegFileBase;
      sendReq (memReq: forall ty, ty OutReq -> ActionT ty (Maybe immResK)) ty: ty inReqK -> ActionT ty Bool;
      callback: forall {ty}, ty InRes -> ActionT ty Void;
      callbackRule (callback: forall {ty}, ty OutRes -> ActionT ty Void): forall {ty}, ActionT ty Void;
    }.
End Ifc.
