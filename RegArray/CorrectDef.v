Require Import Kami.All.
Require Import StdLibKami.RegArray.Impl.
Require Import StdLibKami.RegArray.Ifc.
Require Import StdLibKami.RegArray.Spec.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import Kami.GallinaModules.Relations.
Require Import Coq.Logic.EqdepFacts.

Section CorrectDef.
  
  Context `{Params : RegArray.Ifc.Params}.
  Record RegArrayCorrect (imp spec: RegArray.Ifc.Ifc): Type :=
    {
      regArrayRegs : list (Attribute FullKind);
      regArrayR : RegsT -> RegsT -> Prop;
      readCorrect : forall idx, EffectlessRelation regArrayR (@read _ imp type idx)
                                                   (@read _ spec type idx);
      readWb : forall idx, ActionWb regArrayRegs (@read _ imp type idx);
      writeCorrect : forall val, EffectfulRelation regArrayR (@write _ imp type val) (@write _ spec type val);
      writeWb : forall val, ActionWb regArrayRegs (@write _ imp type val);
    }.
End CorrectDef.
