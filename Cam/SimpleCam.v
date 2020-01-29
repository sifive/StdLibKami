Require Import Kami.AllNotations.
Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.ReplacementPolicy.Ifc.

Section cam.
  Axiom cheat : forall A, A.

  Open Scope kami_expr.
  Open Scope kami_action.

  Class SimpleCamParams := {
    regName : string;
    size : nat;
    policy: ReplacementPolicy size;
    camParamsInst : CamParams
  }.

  Section instance.
    Variable (params: SimpleCamParams).

    Local Definition Index : Kind := Bit (Nat.log2_up size).

    Instance SimpleCam : Cam camParamsInst
      := {| 
           read
             := fun ty tag ctxt
                  => Read xs
                       :  Array size (Maybe (Pair keyK dataK))
                       <- regName;
                     utila_acts_find_pkt
                       (map
                         (fun i : nat
                           => LET x 
                                :  Maybe (Pair keyK dataK)
                                <- #xs@[$i : Index @# ty];
                              Ret (STRUCT {
                                  "valid"
                                    ::= #x @% "valid" &&
                                        matchRead tag ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd");
                                  "data"
                                    ::= #x @% "data" @% "snd"
                                } : Maybe dataK @# ty))
                          (seq 0 size));

           write
             := fun ty tag val
                  => LETA index : Index <- @getVictim _ policy ty;
                     Read xs
                       :  Array size (Maybe (Pair keyK dataK))
                       <- regName;
                     LET value
                       :  Pair keyK dataK
                       <- STRUCT {
                            "fst"  ::= tag;
                            "snd" ::= val
                          };
                     Write regName
                       <- #xs@[#index <- STRUCT {"valid" ::= $$true; "data" ::= #value}];
                     Retv;

           flush
             := fun ty
                  => Write regName
                       :  Array size (Maybe (Pair keyK dataK))
                       <- $$(getDefaultConst
                              (Array size
                                (Maybe
                                (Pair (@keyK camParamsInst)
                                   (@dataK camParamsInst)))));
                             
                     Retv;
           clear
             := fun ty tag ctxt
                  => Read xs
                       :  Array size (Maybe (Pair keyK (@dataK camParamsInst)))
                       <- regName;
                     GatherActions
                       (map
                         (fun i : nat
                            => LET x : Maybe (Pair keyK dataK)
                                 <- #xs@[$i : Index @# ty];
                               If matchClear tag ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd")
                                 then
                                   Write regName
                                     :  Array size (Maybe (Pair keyK dataK))
                                     <- #xs@[($i : Index @# ty)
                                          <- unpack (Maybe (Pair keyK dataK)) $0];
                                   Retv;
                               Retv)
                          (seq 0 size))
                       as _;
                     Retv
         |}.
  End instance.
End cam.
