(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class CamParams
    := {
         Key : Kind;
         Data : Kind;
         ReadCtxt : Kind;
         ClearCtxt : Kind;
         MatchRead : forall ty, Key @# ty -> ReadCtxt @# ty -> Key @# ty -> Data @# ty -> Bool @# ty;
         MatchClear: forall ty, Key @# ty -> ClearCtxt @# ty -> Key @# ty -> Data @# ty -> Bool @# ty
    }.

  Section interface.
    Variable camParams : CamParams.
  
    Record Cam
      := {
           read: forall ty, Key @# ty -> ReadCtxt @# ty -> ActionT ty (Maybe Data);
           write: forall ty, Key @# ty -> Data @# ty -> ActionT ty Void;
           flush: forall ty, ActionT ty Void;
           clear: forall ty, Key @# ty -> ClearCtxt @# ty -> ActionT ty Void
      }.

  End interface.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
