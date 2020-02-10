Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section Freelist.
  Class FreeListParams
    := {
         name  : string;
         tagSz : nat;
         (* len   := Nat.pow 2 tagSz; *)
         
       }.

  Section freelistParams.
    Context {freeListParams : FreeListParams}.

    Let k := Bit tagSz. (* (Nat.log2_up len). *)
    Class FreeList: Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        length: nat;
        initialize: forall {ty}, ActionT ty Void;
        nextToAlloc: forall {ty}, ActionT ty (Maybe k);
        alloc: forall {ty}, ty k -> ActionT ty Bool;
        free: forall {ty}, ty k -> ActionT ty Void;
      }.
  End freelistParams.
End Freelist.
