Require Import Kami.AllNotations.

Section interface.
  Open Scope kami_expr.
  Open Scope kami_action.

  Variable size : nat.
  Definition Index := Bit (Nat.log2_up size).

  Record ReplacementPolicy
    := {
         getVictim : forall ty, ActionT ty Index;
         access : forall ty, Index @# ty -> ActionT ty Void
       }.

  Close Scope kami_action.
  Close Scope kami_expr.

End interface.
