(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class CamParams
    := {
         key : Kind;
         data : Kind;
         readCtxt : Kind;
         clearCtxt : Kind;
         matchRead : forall ty, key @# ty -> readCtxt @# ty -> key @# ty -> data @# ty -> Bool @# ty;
         matchClear: forall ty, key @# ty -> clearCtxt @# ty -> key @# ty -> data @# ty -> Bool @# ty
    }.

  Section interface.
    Variable camParams : CamParams.
  
    Class Cam
      := {
           read: forall ty, key @# ty -> readCtxt @# ty -> ActionT ty (Maybe data);
           write: forall ty, key @# ty -> data @# ty -> ActionT ty Void;
           flush: forall ty, ActionT ty Void;
           clear: forall ty, key @# ty -> clearCtxt @# ty -> ActionT ty Void
      }.

  End interface.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
