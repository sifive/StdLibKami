Require Import Kami.AllNotations.
Require Import String.

Section Ifc.
  Class Params := { name : string ;
                    k    : Kind ;
                    size : nat ;
                    init : option (ConstT k)
                  }.

  Context {params: Params}.

  Record Ifc := { regs: list RegInitT;
                  regFiles: list RegFileBase;
                  read ty (idx: ty (Bit (Nat.log2_up size))): ActionT ty k;
                  write ty (writeRq: ty (WriteRq (Nat.log2_up size) k)): ActionT ty Void;
                }.
End Ifc.
