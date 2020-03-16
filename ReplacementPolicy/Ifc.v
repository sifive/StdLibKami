Require Import Kami.AllNotations.

Section Ifc.
  Class Params := { name : string;
                    size  : nat;
                    Index := Bit (Nat.log2_up size) }.

  Context {params: Params}.

  Record Ifc := { regs: list RegInitT;
                  regFiles: list RegFileBase;
                  getVictim : forall ty, ActionT ty Index;
                  access : forall ty, Index @# ty -> ActionT ty Void }.
End Ifc.
