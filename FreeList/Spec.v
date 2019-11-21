Require Import Kami.AllNotations.
Require Import StdLibKami.FreeList.Ifc.
Section FreeListSpec.
  Class FreeListParams := {
                           TagSize: nat;
                           ArrayRegName: string;
                         }.

  Section withParams.
    Context `{FreeListParams}.
    
    Definition len := Nat.pow 2 TagSize. (* length of the freelist *)
    Definition CastTagSize := Nat.log2_up len.
    Definition Tag := Bit CastTagSize.

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    (* Initialization rule, which will fill the free list *)
    Definition initialize ty: ActionT ty Void := Retv.

    Definition nextToAlloc ty: ActionT ty (Maybe Tag) := 
      Read freeArray: Array len Bool <- ArrayRegName;
      Nondet random: Tag;
      LET randomOk: Bool <- #freeArray@[#random];
      LET res: Maybe Tag <- STRUCT { "valid" ::= !#randomOk;
                                     "data" ::= #random };
      Ret #res.
  
    Definition alloc ty (a: ty Tag): ActionT ty Bool := 
      Read freeArray: Array len Bool <- ArrayRegName;
      LET res: Bool <- #freeArray@[#a];
      Write ArrayRegName: Array len Bool <- #freeArray@[#a <- IF #res then #res else $$true];
      Ret !#res.
  
    Definition free ty (tag: ty Tag): ActionT ty Void :=
      Read freeArray: Array len Bool <- ArrayRegName;                                                        
      Write ArrayRegName: Array len Bool <- #freeArray@[#tag <- $$false];
      Retv.

    Definition specFreeList: FreeList := Build_FreeList len initialize nextToAlloc
                                                        alloc free.
  End withParams.
End FreeListSpec.
