Require Import Kami.AllNotations.
Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.ReplacementPolicy.Ifc.

Section cam.
  Context {camParams : CamParams}.

  Local Definition regName := (StdLibKami.Cam.Ifc.name ++ ".regName")%string.

  Open Scope kami_expr.
  Open Scope kami_action.

  Instance PolicyParams : PolicyParams := {|
    ReplacementPolicy.Ifc.name := (StdLibKami.Cam.Ifc.name ++ ".replacementPolicy")%string;
    ReplacementPolicy.Ifc.num  := StdLibKami.Cam.Ifc.num
  |}.

  Class SimpleCamParams := {
    (* regName : string; *)
    (* size : nat; *)
    policy: @ReplacementPolicy PolicyParams;
    camParamsInst : CamParams
  }.

  Section instance.
    Variable (params: SimpleCamParams).

    Local Definition Index : Kind := Bit (Nat.log2_up (StdLibKami.Cam.Ifc.num)).

    Instance SimpleCam : Cam camParamsInst
      := {| 
           read
             := fun ty tag ctxt
                  => Read xs
                       :  Array (StdLibKami.Cam.Ifc.num) (Maybe (Pair keyK dataK))
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
                          (seq 0 (StdLibKami.Cam.Ifc.num)));

           write
             := fun ty tag val
                  => LETA index : Index <- @getVictim _ policy ty;
                     Read xs
                       :  Array (StdLibKami.Cam.Ifc.num) (Maybe (Pair keyK dataK))
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
                       :  Array (StdLibKami.Cam.Ifc.num) (Maybe (Pair keyK dataK))
                       <- $$(getDefaultConst
                              (Array (StdLibKami.Cam.Ifc.num)
                                (Maybe
                                (Pair (@keyK camParamsInst)
                                   (@dataK camParamsInst)))));
                             
                     Retv;
           clear
             := fun ty tag ctxt
                  => Read xs
                       :  Array (StdLibKami.Cam.Ifc.num) (Maybe (Pair keyK (@dataK camParamsInst)))
                       <- regName;
                     GatherActions
                       (map
                         (fun i : nat
                            => LET x : Maybe (Pair keyK dataK)
                                 <- #xs@[$i : Index @# ty];
                               If matchClear tag ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd")
                                 then
                                   Write regName
                                     :  Array (StdLibKami.Cam.Ifc.num) (Maybe (Pair keyK dataK))
                                     <- #xs@[($i : Index @# ty)
                                          <- unpack (Maybe (Pair keyK dataK)) $0];
                                   Retv;
                               Retv)
                          (seq 0 (StdLibKami.Cam.Ifc.num)))
                       as _;
                     Retv
         |}.
  End instance.
End cam.
