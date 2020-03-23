Require Import Kami.AllNotations.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import StdLibKami.Cam.Ifc.

Section Impl.
  Context {ifcParams: Ifc.Params}.

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Class Params :=
    {
      size : nat;
      policy: @ReplacementPolicy.Ifc.Ifc {|
                  ReplacementPolicy.Ifc.name := (name ++ ".replacementPolicy")%string;
                  ReplacementPolicy.Ifc.size := size
                |};
  }.

  Context {params: Params}.

  Local Definition Index := Bit (Nat.log2_up size).
  
  Local Open Scope kami_scope.

  Local Notation array i := (name ++ ".array_" ++ natToHexStr i)%string.
  Definition impl: Ifc
    := {| 
         regs
           := ReplacementPolicy.Ifc.regs policy ++
              map (fun i => (array i,
                             existT RegInitValT (SyntaxKind (Maybe (Pair keyK dataK)))
                                    (Some (SyntaxConst (getDefaultConst (Maybe (Pair keyK dataK))))))%string)
                  (seq 0 size);
         regFiles
           := ReplacementPolicy.Ifc.regFiles policy;
         read
           := fun ty key ctxt
                => utila_acts_find_pkt
                     (map
                       (fun i : nat
                         => Read x: Maybe (Pair keyK dataK) <- array i;
                            LET isMatch <-  #x @% "valid" && matchRead key ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd");
                            If #isMatch
                            then ReplacementPolicy.Ifc.access policy $i;
                            Ret (STRUCT { "valid" ::= #isMatch ;
                                          "data" ::= #x @% "data" @% "snd" } : Maybe dataK @# ty))
                        (seq 0 size));

         write
           := fun ty key data
                => GatherActions
                     (map
                        (fun i =>
                           LETA index : Index <- ReplacementPolicy.Ifc.getVictim policy ty;
                           If ($i == #index)
                           then Write (array i): Maybe (Pair keyK dataK) <- Valid (STRUCT { "fst" ::= key;
                                                                                           "snd" ::= data }); Retv;
                           Retv
                        )
                        (seq 0 size)) as _;
                   Retv;

         flush
           := fun ty
                => GatherActions
                     (map
                        (fun i =>
                           Write (array i): Maybe (Pair keyK dataK) <- Invalid;
                           Retv
                        )
                        (seq 0 size)) as _;
                   Retv;
         clear
           := fun ty key ctxt
                => GatherActions
                     (map
                       (fun i : nat
                          => Read x : Maybe (Pair keyK dataK) <- array i;
                             If matchClear key ctxt (#x @% "data" @% "fst") (#x @% "data" @% "snd")
                             then Write (array i) <- $$(getDefaultConst (Maybe (Pair keyK dataK))); Retv;
                             Retv)
                        (seq 0 size))
                     as _;
                   Retv
      |}.
End Impl.
