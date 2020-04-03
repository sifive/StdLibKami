Require Import Kami.Lib.EclecticLib.
Require Import Kami.All.
Require Import Kami.GallinaModules.Relations.
Require Import Kami.GallinaModules.AuxLemmas.
Require Import Kami.GallinaModules.AuxTactics.
Require Import StdLibKami.RegArray.CorrectDef.
Require Import StdLibKami.Fifo.Ifc.
Require Import StdLibKami.Fifo.GenericSpec.
Require Import StdLibKami.Fifo.DoubleFifo.
Require Import StdLibKami.Fifo.CorrectDef.


Section Proofs.
  Context {ifcParams' : Fifo.Ifc.Params}.
  Context {dblParams' : Fifo.DoubleFifo.Params}.
  
  Local Definition fifoImpl1 := @Fifo.DoubleFifo.impl ifcParams' dblParams'.
  Local Definition fifoImpl2 := @Fifo.GenericSpec.spec ifcParams'.

  Record myFifoImpl1R  (implRegs : RegsT) (fifo1_bval : bool) (fifo1_dval : type k)
         (o_i o_s : RegsT) : Prop :=
    {
      implRegVal : implRegs = [(Fifo1.validRegName,
                                existT _ (SyntaxKind Bool) fifo1_bval);
                              (Fifo1.dataRegName,
                               existT _ (SyntaxKind k) fifo1_dval)];
      Ho_iCorrect1 : o_i = implRegs;
      Ho_sCorrect1 : o_s = implRegs;
      Ho_iNoDup1 : NoDup (map fst o_i);
      Ho_sNoDup1 : NoDup (map fst o_s);
    }.

  
End Proofs.
