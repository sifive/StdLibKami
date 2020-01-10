(*
  Represents a free list that uses a boolean array register rather
  than a Fifo.
*)
Require Import Kami.AllNotations.
Require Import Kami.Utila.
Require Import StdLibKami.FreeList.Ifc.

Section arrayFreeList.

  Class ArrayFreeListParams
    := {
         Len : nat;
         ArrayRegName : string;
       }.

  Section arrayFreeListParams.
    Context `{ArrayFreeListParams}.
    
    Definition TagSize := Nat.log2_up Len.
    Definition Tag := Bit TagSize.


    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition initialize ty: ActionT ty Void :=
      Write ArrayRegName: Array Len Bool <- BuildArray (fun _ => $$false);
      Retv.

    Definition nextToAlloc ty: ActionT ty (Maybe Tag) := 
      Read freeArray: Array Len Bool <- ArrayRegName;
      Ret (fold_left
             (fun (tag : Maybe Tag @# ty) (index : nat)
              => (IF tag @% "valid"
                  then tag
                  else STRUCT {
                           "valid" ::= !(#freeArray@[$index : Tag @# ty]);
                           "data" ::= ($index : Tag @# ty)
                         }))
                   (seq 0 Len)
             Invalid).
  
    Definition alloc ty (tag: ty Tag): ActionT ty Bool := 
      Read freeArray: Array Len Bool <- ArrayRegName;
      LET res: Bool <- #freeArray@[#tag];
      Write ArrayRegName: Array Len Bool <- #freeArray@[#tag <- $$true];
      Ret !#res.
  
    Definition free ty (tag: ty Tag): ActionT ty Void :=
      Read freeArray: Array Len Bool <- ArrayRegName;                                                        
      Write ArrayRegName: Array Len Bool <- #freeArray@[#tag <- $$false];
      Retv.

    Definition regs: list RegInitT := makeModule_regs ( Register ArrayRegName: Array Len Bool <- Default )%kami.

    Instance arrayFreeList: FreeList :=
      {|
        FreeList.Ifc.regs := regs;
        FreeList.Ifc.regFiles := nil;
        FreeList.Ifc.length := Len;
        FreeList.Ifc.initialize := initialize;
        FreeList.Ifc.nextToAlloc := nextToAlloc;
        FreeList.Ifc.alloc := alloc;
        FreeList.Ifc.free := free
      |}.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.

  End arrayFreeListParams.
End arrayFreeList.
