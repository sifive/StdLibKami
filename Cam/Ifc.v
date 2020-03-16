Require Import Kami.AllNotations.

Section Ifc.
  Class Params
    := {
         name : string;
         keyK : Kind;
         dataK : Kind;
         readCtxtK : Kind;
         clearCtxtK : Kind;
         matchRead : forall ty, keyK @# ty -> readCtxtK @# ty -> keyK @# ty -> dataK @# ty -> Bool @# ty;
         matchClear: forall ty, keyK @# ty -> clearCtxtK @# ty -> keyK @# ty -> dataK @# ty -> Bool @# ty
    }.

  Context {params : Params}.
  
  Record Ifc
    := {
        regs: list RegInitT;
        regFiles: list RegFileBase;
        read: forall ty, keyK @# ty -> readCtxtK @# ty -> ActionT ty (Maybe dataK);
        write: forall ty, keyK @# ty -> dataK @# ty -> ActionT ty Void;
        flush: forall ty, ActionT ty Void;
        clear: forall ty, keyK @# ty -> clearCtxtK @# ty -> ActionT ty Void
      }.
End Ifc.
