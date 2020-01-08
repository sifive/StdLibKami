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
         TagSize : nat;
         ArrayRegName : string;
       }.

  Section arrayFreeListParams.
    Context `{ArrayFreeListParams}.
    
    Definition len := Nat.pow 2 TagSize. (* length of the freelist *)
    Definition CastTagSize := Nat.log2_up len.
    Definition Tag := Bit CastTagSize.


    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Definition initialize ty: ActionT ty Void :=
      Write ArrayRegName: Array len Bool <- BuildArray (fun _ => $$false);
      Retv.

    Definition nextToAlloc ty: ActionT ty (Maybe Tag) := 
      Read freeArray: Array len Bool <- ArrayRegName;
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
  
    Definition alloc ty (tag: ty Tag): ActionT ty Bool := 
      Read freeArray: Array len Bool <- ArrayRegName;
      LET res: Bool <- #freeArray@[#tag];
      Write ArrayRegName: Array len Bool <- #freeArray@[#tag <- $$true];
      Ret !#res.
  
    Definition free ty (tag: ty Tag): ActionT ty Void :=
      Read freeArray: Array len Bool <- ArrayRegName;                                                        
      Write ArrayRegName: Array len Bool <- #freeArray@[#tag <- $$false];
      Retv.

    Definition regs: list RegInitT := makeModule_regs ( Register ArrayRegName: Array len Bool <- Default )%kami.

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

  End arrayFreeListParams.
End arrayFreeList.
