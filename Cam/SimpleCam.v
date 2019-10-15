Require Import Kami.AllNotations.
Require Import StdLibKami.Cam.Interface.
Require Import StdLibKami.ReplacementPolicy.Interface.

Section cam.
  Axiom cheat : forall A, A.

  Open Scope kami_expr.
  Open Scope kami_action.

  Record SimpleCam := {
    Tag : Kind;
    Data : Kind;
    ReadCtxt : Kind;
    ClearCtxt : Kind;

    regName : string;
    size : nat;

    Index : Kind := Bit (Nat.log2_up size);
    policy : ReplacementPolicy Index;

    camMatchRead : forall ty, Tag @# ty -> ReadCtxt @# ty -> Tag @# ty -> Bool @# ty;
    camMatchClear: forall ty, Tag @# ty -> ClearCtxt @# ty -> Tag @# ty -> Bool @# ty;

    camRead
      :  forall ty, Tag @# ty -> ReadCtxt @# ty -> ActionT ty (Maybe Data)
      := fun ty tag ctxt
           => Read xs
                :  Array size (Maybe (Pair Tag Data))
                <- regName;
              utila_acts_find_pkt
                (map
                  (fun i : nat
                    => LET x 
                         :  Maybe (Pair Tag Data)
                         <- #xs@[$i : Index @# ty];
                       Ret (STRUCT {
                           "valid"
                             ::= #x @% "valid" &&
                                 camMatchRead tag ctxt (#x @% "data" @% "fst");
                           "data"
                             ::= #x @% "data" @% "snd"
                         } : Maybe Data @# ty))
                   (seq 0 size));

    camWrite
      :  forall ty, Tag @# ty -> Data @# ty -> ActionT ty Void
      := fun ty tag data
           => LETA index : Index <- getVictim policy ty;
              Read xs
                :  Array size (Maybe (Pair Tag Data))
                <- regName;
              LET value
                :  Pair Tag Data
                <- STRUCT {
                     "fst"  ::= tag;
                     "snd" ::= data
                   };
              Write regName
                <- #xs@[#index <- STRUCT {"valid" ::= $$true; "data" ::= #value}];
              Retv;
    
    camFlush
      :  forall ty, ActionT ty Void
      := fun ty
           => Write regName <- unpack (Array size (Maybe (Pair Tag Data))) $0;
              Retv;

    camClear
      :  forall ty, Tag @# ty -> ClearCtxt @# ty -> ActionT ty Void
      := fun ty tag ctxt
           => Read xs
                :  Array size (Maybe (Pair Tag Data))
                <- regName;
              GatherActions
                (map
                  (fun i : nat
                     => LET x : Maybe (Pair Tag Data)
                          <- #xs@[$i : Index @# ty];
                        If camMatchClear tag ctxt (#x @% "data" @% "fst")
                          then
                            Write regName
                              <- #xs@[($i : Index @# ty)
                                   <- $$(getDefaultConst (Maybe (Pair Tag Data)))];
                            Retv;
                        Retv)
                   (seq 0 size))
                as _;
              Retv;

    camInst
      :  Cam
      := Build_Cam camMatchRead camMatchClear camRead camWrite camFlush camClear
  }.

  Close Scope kami_action.
  Close Scope kami_expr.

End cam.
