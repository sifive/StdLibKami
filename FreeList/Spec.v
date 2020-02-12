Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section FreeListSpec.
  Context {freeListParams : FreeListParams}.

  Local Definition arrayRegName := (name ++ ".data")%string.

(*
  Class FreeListParams := {
                           tagSize: nat;
                           arrayRegName: string;
                         }.
*)
  Section withParams.
    Context `{FreeListParams}.
    
    Local Definition len := Nat.pow 2 tagSz.
    Definition CastTagSize := Nat.log2_up (Nat.pow 2 tagSz).
    Definition Tag := Bit tagSz.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition initialize ty: ActionT ty Void :=
      Write arrayRegName: Array len Bool <- BuildArray (fun _ => $$false);
      Retv.

    Definition nextToAlloc ty: ActionT ty (Maybe Tag) := 
      Read freeArray: Array len Bool <- arrayRegName;
      Nondet random: Tag;
      LET randomOk: Bool <- #freeArray@[#random];
      LET res: Maybe Tag <- STRUCT { "valid" ::= !#randomOk;
                                     "data" ::= #random };
      Ret #res.
  
    Definition alloc ty (tag: ty Tag): ActionT ty Bool := 
      Read freeArray: Array len Bool <- arrayRegName;
      LET res: Bool <- #freeArray@[#tag];
      Write arrayRegName: Array len Bool <- #freeArray@[#tag <- $$true];
      Ret !#res.
  
    Definition free ty (tag: ty Tag): ActionT ty Void :=
      Read freeArray: Array len Bool <- arrayRegName;                                                        
      Write arrayRegName: Array len Bool <- #freeArray@[#tag <- $$false];
      Retv.

    Definition regs: list RegInitT := makeModule_regs ( Register arrayRegName: Array len Bool <- Default )%kami.

    Instance specFreeList: FreeList := 
      {|
        FreeList.Ifc.regs := regs;
        FreeList.Ifc.regFiles := nil;
        FreeList.Ifc.length := len;
        FreeList.Ifc.initialize := initialize;
        FreeList.Ifc.nextToAlloc := nextToAlloc;
        FreeList.Ifc.alloc := alloc;
        FreeList.Ifc.free := free
      |}.
        
    Local Close Scope kami_action.
    Local Close Scope kami_expr.

  End withParams.
End FreeListSpec.
