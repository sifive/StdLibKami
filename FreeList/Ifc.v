Require Import Kami.AllNotations.

Section Ifc.
  Class Params := { name : string;
                    size : nat;
                    lgSize := Nat.log2_up size }.
  
  Context {params : Params}.

  Record Ifc: Type :=
    {
      regs: list RegInitT;
      regFiles: list RegFileBase;
      initialize: forall {ty}, ActionT ty Void;
      nextToAlloc: forall {ty}, ActionT ty (Maybe (Bit lgSize));
      alloc: forall {ty}, ty (Bit lgSize) -> ActionT ty Bool;
      free: forall {ty}, ty (Bit lgSize) -> ActionT ty Void;
    }.
End Ifc.
