(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Record Cam
    := {
         Tag : Kind;
         Data : Kind;
         ReadCtxt : Kind;
         ClearCtxt : Kind;
         matchRead : forall ty, Tag @# ty -> ReadCtxt @# ty -> Tag @# ty -> Bool @# ty;
         matchClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> Tag @# ty -> Bool @# ty;
         camRead: forall ty, Tag @# ty -> ReadCtxt @# ty -> ActionT ty (Maybe Data);
         camWrite: forall ty, Tag @# ty -> Data @# ty -> ActionT ty Void;
         camFlush: forall ty, ActionT ty Void;
         camClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> ActionT ty Void
    }.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
