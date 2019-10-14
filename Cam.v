(* Content Addressable Memory *)
Require Import Wf.
Require Import Wf_nat.
Require Import Kami.AllNotations.

Axiom cheat : forall A, A.

Section cam.
  Open Scope kami_expr.
  Open Scope kami_action.

  Class Cam
    (Tag Data ReadCtxt ClearCtxt : Kind)
    (regNames : list string)
    := {
      matchRead: forall ty, Tag @# ty -> ReadCtxt @# ty -> Tag @# ty -> Bool @# ty;

      matchClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> Tag @# ty -> Bool @# ty;

      camRead
        (ty : Kind -> Type)
        (tag : Tag @# ty)
        (ctxt : ReadCtxt @# ty)
        : ActionT ty (Maybe Data)
        := utila_acts_find_pkt
             (map
               (fun regName : string
                 => Read entry : Maybe (Pair Tag Data) <- regName;
                    utila_acts_opt_pkt
                      (#entry @% "data" @% "snd")
                      (#entry @% "valid" &&
                       matchRead tag ctxt (#entry @% "data" @% "fst")))
                regNames);

      camWrite
        (ty : Kind -> Type)
        (tag : Tag @# ty)
        (data : Data @# ty)
        :  ActionT ty Void
        := cheat _;

      camFlush: forall ty, ActionT ty Void := cheat _;

      camClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> ActionT ty Void := cheat _;
    }.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
