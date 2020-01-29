(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class CamParams
    := {
         keyK : Kind;
         dataK : Kind;
         readCtxtK : Kind;
         clearCtxtK : Kind;
         matchRead : forall ty, keyK @# ty -> readCtxtK @# ty -> keyK @# ty -> dataK @# ty -> Bool @# ty;
         matchClear: forall ty, keyK @# ty -> clearCtxtK @# ty -> keyK @# ty -> dataK @# ty -> Bool @# ty
    }.

  Section interface.
    Variable camParams : CamParams.
  
    Class Cam
      := {
           read: forall ty, keyK @# ty -> readCtxtK @# ty -> ActionT ty (Maybe dataK);
           write: forall ty, keyK @# ty -> dataK @# ty -> ActionT ty Void;
           flush: forall ty, ActionT ty Void;
           clear: forall ty, keyK @# ty -> clearCtxtK @# ty -> ActionT ty Void
      }.

  End interface.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
