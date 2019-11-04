Require Import Kami.All.
Section DevRouter.
  Context {ty: Kind -> Type}.
  Record DeviceData (reqK respK: Kind): Type :=
    {
      devReq: ty reqK -> ActionT ty Bool;
      devPoll: ActionT ty (Maybe respK)
    }.
  Class DevRouterParams :=
    {
      reqK: Kind;
      respK: Kind;
      devices: list (DeviceData reqK respK);
      numDevices: nat := List.length devices;
     
      clientCallback: ty respK -> ActionT ty Void
    }.


  Section withParams.
    Context `{DevRouterParams}.
    Record DevRouter: Type :=
      {
        (* Rules *)
        pollRules: list (ActionT ty Void);
        devRouterReqs: list (ty reqK -> ActionT ty Bool);
      }.
  End withParams.
End DevRouter.
