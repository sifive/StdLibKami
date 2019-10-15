Require Import Kami.AllNotations.
Require Import StdLibKami.Cam.Interface.
Require Import StdLibKami.ReplacementPolicy.Interface.

Section cam.
  Axiom cheat : forall A, A.

  Open Scope kami_expr.
  Open Scope kami_action.

  Class Params := {
    regName : string;
    size : nat;
    policy: ReplacementPolicy.Interface.Ifc size;
    CamParams : Cam.Interface.Params
  }.

  Section instance.
    Context `{params: Params}.

    Local Definition Index : Kind := Bit (Nat.log2_up size).

    Definition simpleCam : Cam.Interface.Ifc CamParams
      := {| 
           read
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
                                        matchRead tag ctxt (#x @% "data" @% "fst");
                                  "data"
                                    ::= #x @% "data" @% "snd"
                                } : Maybe Data @# ty))
                          (seq 0 size));

           write
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

           flush
             := fun ty
                  => Write regName
                       :  Array size (Maybe (Pair Tag Data))
                       <- $$(getDefaultConst
                              (Array size
                                (Maybe
                                  (Pair (@Tag CamParams)
                                        (@Data CamParams)))));
                             
                     Retv;
           clear
             := fun ty tag ctxt
                  => Read xs
                       :  Array size (Maybe (Pair (@Tag CamParams) (@Data CamParams)))
                       <- regName;
                     GatherActions
                       (map
                         (fun i : nat
                            => LET x : Maybe (Pair Tag Data)
                                 <- #xs@[$i : Index @# ty];
                               If matchClear tag ctxt (#x @% "data" @% "fst")
                                 then
                                   Write regName
                                     :  Array size (Maybe (Pair Tag Data))
                                     <- #xs@[($i : Index @# ty)
                                          <- unpack (Maybe (Pair Tag Data)) $0];
                                   Retv;
                               Retv)
                          (seq 0 size))
                       as _;
                     Retv
         |}.
  End instance.
End cam.
