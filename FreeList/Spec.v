Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section FreeListSpec.
  Context {ifcParams : Ifc.Params}.

  Local Definition arrayRegName := (name ++ ".data")%string.

  Local Definition Tag := Bit lgSize.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Local Definition initialize ty: ActionT ty Void :=
    Write arrayRegName: Array size Bool <- BuildArray (fun _ => $$false);
    Retv.

  Local Definition nextToAlloc ty: ActionT ty (Maybe Tag) := 
    Read freeArray: Array size Bool <- arrayRegName;
    Nondet random: Tag;
    LET randomOk: Bool <- #freeArray@[#random];
    LET res: Maybe Tag <- STRUCT { "valid" ::= !#randomOk;
                                   "data" ::= #random };
    Ret #res.

  Local Definition alloc ty (tag: ty Tag): ActionT ty Bool := 
    Read freeArray: Array size Bool <- arrayRegName;
    LET res: Bool <- #freeArray@[#tag];
    Write arrayRegName: Array size Bool <- #freeArray@[#tag <- $$true];
    Ret !#res.

  Local Definition free ty (tag: ty Tag): ActionT ty Void :=
    Read freeArray: Array size Bool <- arrayRegName;                                                        
    Write arrayRegName: Array size Bool <- #freeArray@[#tag <- $$false];
    Retv.

  Local Definition regs: list RegInitT := makeModule_regs ( Register arrayRegName: Array size Bool <- Default )%kami.

  Definition impl: Ifc := 
    {|
      Ifc.regs := regs;
      Ifc.regFiles := nil;
      Ifc.initialize := initialize;
      Ifc.nextToAlloc := nextToAlloc;
      Ifc.alloc := alloc;
      Ifc.free := free
    |}.
      
  Local Close Scope kami_action.
  Local Close Scope kami_expr.

End FreeListSpec.
