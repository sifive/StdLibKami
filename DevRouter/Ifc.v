Require Import Kami.All.
Section DevRouter.
  Context {reqResK: Kind}.
  Record DeviceData (reqK respK: Kind): Type :=
    {
      devReq: forall {ty}, ty reqK -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                         "info" :: reqResK };
      devPoll: forall {ty}, ActionT ty (Maybe respK)
    }.

  Class DevRouterParams :=
    {
      reqK: Kind;
      respK: Kind;
      devices: list (DeviceData reqK respK);
      numDevices: nat := List.length devices;
      
      clientCallback: forall {ty}, ty respK -> ActionT ty Void
    }.


  Section withParams.
    Context `{DevRouterParams}.
    Record DevRouter : Type :=
      {
        (* Rules *)
        pollRules: list (forall {ty}, ActionT ty Void);
        devRouterReqs: list (forall {ty}, ty reqK -> ActionT ty STRUCT_TYPE { "ready" :: Bool;
                                                                        "info" :: reqResK });
      }.
  End withParams.
End DevRouter.
