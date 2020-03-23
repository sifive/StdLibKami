Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.


Section Impl.
  Context {ifcParams: Ifc.Params}.

  Local Notation Idx := (Bit (Nat.log2_up size)).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition names := map (fun i => name ++ "_" ++ natToHexStr i)%string (seq 0 size).

  Local Definition read ty (idx: ty Idx) : ActionT ty k :=
   GatherActions (map (fun '(i, reg) => Read val: k <- reg;
                      Ret (IF ($i == #idx)
                           then #val else $$(getDefaultConst k))) (tag names)) as vals;
   Ret (Kor vals).

  Local Definition write ty (writeRq: ty (WriteRq (Nat.log2_up size) k)): ActionT ty Void :=
    GatherActions (map (fun '(i, reg) => Read val: k <- reg;
                                         Write reg: k <- (IF $i == #writeRq @% "addr" then #writeRq @% "data" else #val);
                                         Retv) (tag names)) as _;
    Retv.

  Definition impl := {| regs := map (fun i => (i, existT RegInitValT (SyntaxKind k) match init with
                                                                                    | None => None
                                                                                    | Some x => Some (SyntaxConst x)
                                                                                    end)) names;
                        regFiles := nil;
                        Ifc.read := read;
                        Ifc.write := write |}.
End Impl.
