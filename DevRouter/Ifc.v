Require Import Kami.All.
Record DeviceData (reqK respK: Kind): Type :=
  {
    devReq: forall {ty}, ty reqK -> ActionT ty Bool;
    devPoll: forall {ty}, ActionT ty (Maybe respK)
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
    Record DevRouter : Type :=
      {
        (* Rules *)
        pollRules (clientCallback: forall {ty}, ty respK -> ActionT ty Void): list (forall {ty}, ActionT ty Void);
        devRouterReqs: forall {ty}, ty (STRUCT_TYPE { "dtag" :: Bit (Nat.log2_up numDevices);
                                                      "req" :: reqK }) -> ActionT ty Bool;
      }.
End withParams.

