Require Import Kami.AllNotations.

Section interface.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class PolicyParams := {
    name : string;
    num  : nat;
  }.

  Section policyParams.
    Context {policyParams : PolicyParams}.

    Local Definition Index := Bit (Nat.log2_up num).

    Record ReplacementPolicy
      := {
           getVictim : forall ty, ActionT ty Index;
           access : forall ty, Index @# ty -> ActionT ty Void
         }.

  End policyParams.

  Close Scope kami_action.
  Close Scope kami_expr.

End interface.
