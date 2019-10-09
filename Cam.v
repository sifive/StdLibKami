(* Content Addressable Memory *)
Require Import Kami.AllNotations.

Axiom cheat : forall A, A.

Section cam.
  Variable Tag : Kind.
  Variable Data : Kind.
  Variable ty: Kind -> Type.

  Open Scope kami_expr.
  Open Scope kami_action.

  Definition camRead: Tag @# ty -> ActionT ty (Maybe Data) := cheat _.

  Definition camWrite: Pair Tag Data @# ty -> ActionT ty Void := cheat _.

  Definition camFlush: ActionT ty Void := cheat _.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
