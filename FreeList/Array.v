(*
  Represents a free list that uses a boolean array register rather
  than a Fifo.
*)
Require Import Kami.AllNotations.
Require Import Kami.Utila.
Require Import StdLibKami.FreeList.Ifc.

Section array.
  Context {freeListParams : FreeListParams}.

  Local Definition arrayRegName := (name ++ ".data")%string.

  Section arrayParams.
    Local Definition len := Nat.pow 2 tagSz.
    Local Definition Tag := Bit tagSz.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Local Definition initialize ty: ActionT ty Void :=
      Write arrayRegName: Array len Bool <- BuildArray (fun _ => $$false);
      Retv.

    Local Definition nextToAlloc ty: ActionT ty (Maybe Tag) := 
      Read freeArray: Array len Bool <- arrayRegName;
      Ret (fold_left
             (fun (tag : Maybe Tag @# ty) (index : nat)
              => (IF tag @% "valid"
                  then tag
                  else STRUCT {
                           "valid" ::= !(#freeArray@[$index : Tag @# ty]);
                           "data" ::= ($index : Tag @# ty)
                         }))
                   (seq 0 len)
             Invalid).
  
    Local Definition alloc ty (tag: ty Tag): ActionT ty Bool := 
      Read freeArray: Array len Bool <- arrayRegName;
      LET res: Bool <- #freeArray@[#tag];
      Write arrayRegName: Array len Bool <- #freeArray@[#tag <- $$true];
      Ret !#res.
  
    Local Definition free ty (tag: ty Tag): ActionT ty Void :=
      Read freeArray: Array len Bool <- arrayRegName;                                                        
      Write arrayRegName: Array len Bool <- #freeArray@[#tag <- $$false];
      Retv.

    Local Definition regs: list RegInitT := makeModule_regs ( Register arrayRegName: Array len Bool <- Default )%kami.

    Definition arrayFreeList: FreeList :=
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

  End arrayParams.
End array.
