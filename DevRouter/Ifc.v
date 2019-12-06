Require Import Kami.All.
Record DeviceData (deviceInfoT: Type) (reqK respK: Kind): Type :=
  {
    memDeviceReq: forall {ty}, ty reqK -> ActionT ty Bool;
    memDevicePoll: forall {ty}, ActionT ty (Maybe respK);
    memDeviceInfo: deviceInfoT
  }.

Class DevRouterParams :=
  {
    reqK: Kind;
    respK: Kind;
    deviceInfoT: Type;
    devices: list (DeviceData deviceInfoT reqK respK);
    numDevices: nat := List.length devices;
  }.

Section withParams.
    Context `{DevRouterParams}.
    Record DevRouter : Type :=
      {
        (* Rules *)
        pollRules (clientCallback: forall {ty}, ty respK -> ActionT ty Void): list (forall {ty}, ActionT ty Void);
        devRouterReq: forall {ty}, ty (STRUCT_TYPE { "tag" :: Bit (Nat.log2_up numDevices);
                                                     "req" :: reqK }) -> ActionT ty Bool;
      }.
End withParams.
