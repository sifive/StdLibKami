Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.

Section Spec.
  Context {ifcParams : Ifc.Params}.
  Local Notation Idx := (Bit (Nat.log2_up size)).
  Local Definition arrayName := (name ++ ".list")%string.
    
  Local Open Scope kami_expr.
  Local Open Scope kami_action.
  
  Local Definition read ty (idx: ty Idx) : ActionT ty k :=
    Read array: (Array size k) <- arrayName;
    Ret (#array @[ #idx]).

  Local Definition write ty (writeRq : ty (WriteRq (Nat.log2_up size) k)): ActionT ty Void :=
    Read array: (Array size k) <- arrayName;
    Write arrayName: (Array size k) <- #array @[ #writeRq @% "addr" <- #writeRq @% "data" ];
    Retv.
  
  Local Definition regs : list RegInitT := makeModule_regs (Register arrayName : (Array size k) <- Default)%kami.

  Definition spec : Ifc :=
    {|
      Ifc.regs := regs;
      Ifc.regFiles := nil;
      Ifc.read := read;
      Ifc.write := write
    |}.

End Spec.
