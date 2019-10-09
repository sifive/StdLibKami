(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Axiom cheat : forall A, A.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Variable ty: Kind -> Type.
  Variable Tag Data ReadCtxt ClearCtxt: Kind.

  Variable matchRead: Tag @# ty -> ReadCtxt @# ty -> Tag @# ty -> Data @# ty -> Bool @# ty.

  Variable matchClear: Tag @# ty -> ClearCtxt @# ty -> Tag @# ty -> Data @# ty -> Bool @# ty.

  Definition camRead: Tag @# ty -> ReadCtxt @# ty -> ActionT ty (Maybe Data) := cheat _.

  Definition camWrite: Tag @# ty -> Data @# ty -> ActionT ty Void := cheat _.

  Definition camFlush: ActionT ty Void := cheat _.

  Definition camClear: Tag @# ty -> ClearCtxt @# ty -> ActionT ty Void := cheat _.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
