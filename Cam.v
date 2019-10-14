(* Content Addressable Memory *)
Require Import Kami.AllNotations.
Require Import StdLibKami.PseudoLru.

Axiom cheat : forall A, A.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Variable Tag Data ReadCtxt ClearCtxt : Kind.
  Variable matchRead: forall ty, Tag @# ty -> ReadCtxt @# ty -> Tag @# ty -> Bool @# ty.
  Variable  matchClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> Tag @# ty -> Bool @# ty.

  Record Cam
    := {
        camRead:
          forall (ty : Kind -> Type)
                 (tag : Tag @# ty)
                 (ctxt : ReadCtxt @# ty),
            ActionT ty (Maybe Data);
        
        camWrite:
          forall (ty : Kind -> Type)
                 (tag : Tag @# ty)
                 (data : Data @# ty),
            ActionT ty Void;
        
      camFlush: forall ty, ActionT ty Void;

      camClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> ActionT ty Void;
    }.

  Section SimpleCam.
    Variable regName : string.
    Variable size : nat.

    Definition SimpleCam : Cam
      := {| camRead :=
              fun ty tag ctxt =>
                utila_acts_find_pkt
                  (map
                     (fun i: nat
                      => Read entry : Maybe (Pair Tag Data) <- regName ++ "__" ++ natToHexStr i;
                           utila_acts_opt_pkt
                             (#entry @% "data" @% "snd")
                             (#entry @% "valid" &&
                               matchRead tag ctxt (#entry @% "data" @% "fst")))
                     (seq 0 size));
            
            camWrite :=
              fun ty tag data => cheat _ ;
            
            camFlush :=
              fun ty => cheat _;

            camClear :=
              fun ty tag ctxt => cheat _ |}.
  End SimpleCam.
    
  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
