(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class CamParams
    := {
         CamTag : Kind;
         CamData : Kind;
         CamReadCtxt : Kind;
         CamClearCtxt : Kind;
         camMatchRead : forall ty, CamTag @# ty -> CamReadCtxt @# ty -> CamTag @# ty -> Bool @# ty;
         camMatchClear: forall ty, CamTag @# ty -> CamClearCtxt @# ty -> CamTag @# ty -> Bool @# ty
    }.

  Section interface.
    Variable camParams : CamParams.
  
    Record Cam
      := {
           camRead: forall ty, CamTag @# ty -> CamReadCtxt @# ty -> ActionT ty (Maybe CamData);
           camWrite: forall ty, CamTag @# ty -> CamData @# ty -> ActionT ty Void;
           camFlush: forall ty, ActionT ty Void;
           camClear: forall ty, CamTag @# ty -> CamClearCtxt @# ty -> ActionT ty Void
      }.

  End interface.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
