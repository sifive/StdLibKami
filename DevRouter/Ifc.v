Require Import Kami.All.
Record DeviceData (reqK respK: Kind): Type :=
  {
    memDeviceReq: forall {ty}, ty reqK -> ActionT ty Bool;
    memDevicePoll: forall {ty}, ActionT ty (Maybe respK)
  }.

Class DevRouterParams :=
  {
    reqK: Kind;
    respK: Kind;
    devices: list (DeviceData reqK respK);
    numDevices: nat := List.length devices;
  }.

Section withParams.
    Context `{DevRouterParams}.

    Definition DevRouterReq
      := STRUCT_TYPE {
           "tag" :: Bit (Nat.log2_up numDevices);
           "req" :: reqK
         }.

    Class DevRouter : Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        devRouterReq: forall {ty}, ty DevRouterReq -> ActionT ty Bool;
        pollRules (clientCallback: forall {ty}, ty respK -> ActionT ty Void): list (forall {ty}, ActionT ty Void);
      }.
End withParams.
