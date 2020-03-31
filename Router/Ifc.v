Require Import Kami.AllNotations.

Section Ifc.
  Record DeviceIfc (reqK respK: Kind): Type :=
    {
      deviceReq: forall {ty}, ty reqK -> ActionT ty Bool;
      devicePoll: forall {ty}, ActionT ty (Maybe respK)
    }.

  Class Params :=
    {
      name: string;
      reqK: Kind;
      respK: Kind;
      devices: list (DeviceIfc reqK respK);
      numDevices := length devices;
    }.

  Context {params: Params}.

  Definition OutReq := STRUCT_TYPE { "dtag" :: Bit (Nat.log2_up numDevices) ;
                                     "req" :: reqK }.

  Record Ifc :=
    {
      regs: list RegInitT;
      regFiles: list RegFileBase;
      sendReq: forall ty, ty OutReq -> ActionT ty Bool;
      pollRules (callback: forall {ty}, ty respK -> ActionT ty Void): list (forall {ty}, ActionT ty Void);
      finishRule: forall ty, ActionT ty Void;
    }.
End Ifc.
