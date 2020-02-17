Require Import Kami.AllNotations.
Require Import StdLibKami.Fifo.Ifc.
Section Freelist.
  Class FreeListParams
    := {
         name  : string;
         tagSz : nat;
       }.

  Section freelistParams.
    Context {freeListParams : FreeListParams}.

    Record FreeList: Type :=
      {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        length: nat;
        initialize: forall {ty}, ActionT ty Void;
        nextToAlloc: forall {ty}, ActionT ty (Maybe (Bit tagSz));
        alloc: forall {ty}, ty (Bit tagSz) -> ActionT ty Bool;
        free: forall {ty}, ty (Bit tagSz) -> ActionT ty Void;
      }.
  End freelistParams.
End Freelist.
