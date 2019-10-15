(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class Params
    := {
         Tag : Kind;
         Data : Kind;
         ReadCtxt : Kind;
         ClearCtxt : Kind;
         matchRead : forall ty, Tag @# ty -> ReadCtxt @# ty -> Tag @# ty -> Bool @# ty;
         matchClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> Tag @# ty -> Bool @# ty
    }.

  Section interface.
    Variable params : Params.
  
    Record Ifc
      := {
           read: forall ty, Tag @# ty -> ReadCtxt @# ty -> ActionT ty (Maybe Data);
           write: forall ty, Tag @# ty -> Data @# ty -> ActionT ty Void;
           flush: forall ty, ActionT ty Void;
           clear: forall ty, Tag @# ty -> ClearCtxt @# ty -> ActionT ty Void
      }.

  End interface.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
