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
         (*
           The name of a boolean array register with pow2 TagSize
           elements.
         *)
         ArrayRegName : string;
       }.

  Section arrayFreeListParams.
    Context {arrayFreeListParams : ArrayFreeListParams}.

    Local Definition len := Nat.pow 2 TagSize.
    Local Definition Tag := Bit (Nat.log2_up len). 

    Local Open Scope kami_expr.
    Local Open Scope kami_action.

    Section ty.
      Variable ty : Kind -> Type.

      Local Definition arrayFreeListInit
        :  ActionT ty Void
        := Write ArrayRegName : Array len Bool <- $$(getDefaultConst (Array len Bool));
           Retv.

      Local Definition arrayFreeListNextToAlloc
        :  ActionT ty (Maybe Tag)
        := Read array : Array len Bool <- ArrayRegName;
           Ret
             (fold_left
                (fun (tag : Maybe Tag @# ty) (index : nat)
                  => IF tag @% "valid"
                       then tag
                       else
                         IF #array@[$index : Tag @# ty]
                           then Valid ($index : Tag @# ty)
                           else Invalid : Maybe Tag @# ty)
                (seq 0 len)
                Invalid).

      (*
        Marks the given tag as "in use," and returns true iff the
        tag was successfully marked as "in use."
      *)
      Local Definition arrayFreeListAlloc
        (tag : ty Tag)
        :  ActionT ty Bool
        := Read array : Array len Bool <- ArrayRegName;
           Write ArrayRegName : Array len Bool <- #array@[#tag <- $$true];
           Ret $$true.

      (*
        Marks the given tag as "free," and returns true iff the
        tag was successfully marked as "free."
      *)
      Local Definition arrayFreeListFree
        (tag : ty Tag)
        :  ActionT ty Void
        := Read array : Array len Bool <- ArrayRegName;
           Write ArrayRegName : Array len Bool <- #array@[#tag <- $$false];
           Retv.

    End ty.

    Open Scope kami_scope.
    Open Scope kami_expr_scope.
    
    Definition regs: list RegInitT := makeModule_regs ( Register ArrayRegName: Array len Bool <- Default ).

    Definition arrayFreeList: FreeList :=
      {|
        FreeList.Ifc.regs := regs;
        length      := len;
        initialize  := arrayFreeListInit;
        nextToAlloc := arrayFreeListNextToAlloc;
        alloc       := arrayFreeListAlloc;
        free        := arrayFreeListFree
      |}.

    Local Close Scope kami_action.
    Local Close Scope kami_expr.

  End arrayFreeListParams.
End arrayFreeList.
