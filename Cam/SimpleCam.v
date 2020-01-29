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
    CamParamsInst : CamParams
  }.

  Section instance.
    Variable (params: SimpleCamParams).

    Local Definition Index : Kind := Bit (Nat.log2_up size).

    Instance SimpleCam : Cam CamParamsInst
      := {| 
           read
             := fun ty tag ctxt
                  => Read xs
                       :  Array size (Maybe (Pair key data))
                       <- regName;
                     utila_acts_find_pkt
                       (map
                         (fun i : nat
                           => LET x 
                                :  Maybe (Pair key data)
                                <- #xs@[$i : Index @# ty];
                              Ret (STRUCT {
                                  "valid"
                                    ::= #x @% "valid" &&
                                        matchRead tag ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd");
                                  "data"
                                    ::= #x @% "data" @% "snd"
                                } : Maybe data @# ty))
                          (seq 0 size));

           write
             := fun ty tag val
                  => LETA index : Index <- @getVictim _ policy ty;
                     Read xs
                       :  Array size (Maybe (Pair key data))
                       <- regName;
                     LET value
                       :  Pair key data
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
                       :  Array size (Maybe (Pair key data))
                       <- $$(getDefaultConst
                              (Array size
                                (Maybe
                                (Pair (@key CamParamsInst)
                                   (@data CamParamsInst)))));
                             
                     Retv;
           clear
             := fun ty tag ctxt
                  => Read xs
                       :  Array size (Maybe (Pair key (@data CamParamsInst)))
                       <- regName;
                     GatherActions
                       (map
                         (fun i : nat
                            => LET x : Maybe (Pair key data)
                                 <- #xs@[$i : Index @# ty];
                               If matchClear tag ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd")
                                 then
                                   Write regName
                                     :  Array size (Maybe (Pair key data))
                                     <- #xs@[($i : Index @# ty)
                                          <- unpack (Maybe (Pair key data)) $0];
                                   Retv;
                               Retv)
                          (seq 0 size))
                       as _;
                     Retv
         |}.
  End instance.
End cam.
