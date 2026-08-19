module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimeFibre
public import Erdos289.SignedInverseAtom
public import Erdos289.StageProfile

@[expose] public section

/-!
# A prime row has simple-fibre multiplicity one

At a prime current the signed-inverse atoms of a row are separated in the simple
fibre by their coefficients alone: the companion part of an atom's observation
lies in the lower stage, so two atoms have the same class exactly when their
distinguished reciprocals do, and `Erdos289.reciprocalResidue_sub_notMem_lower`
says that happens only for equal coefficients.

Both factorization proofs are supplied by
`Erdos289.SignedInverse.atom_factorsThroughPrimePowerStage`.

Consequently a deduplicated prime row injects into the simple fibre, and the
image that feeds the Dias da Silva–Hamidoune interval is as large as the row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/--
Distinct current coefficients give distinct simple-fibre classes at a prime
current.
-/
theorem atom_simpleFiberClass_ne_of_coefficient_ne
    {p b b' : ℕ} {w : ComplementaryPair p b} {w' : ComplementaryPair p b'}
    (hp : p.Prime) (g : GoodOrientation p w) (g' : GoodOrientation p w')
    (hppos : 0 < p) (hb : b < p) (hb' : b' < p)
    (hne : w.coefficient g.sign ≠ w'.coefficient g'.sign)
    (hfac : (g.atom hppos).FactorsThroughPrimePowerStage p)
    (hfac' : (g'.atom hppos).FactorsThroughPrimePowerStage p) :
    (g.atom hppos).simpleFiberClass hfac ≠ (g'.atom hppos).simpleFiberClass hfac' := by
  intro heq
  rw [Support.simpleFiberClass_eq_iff hfac hfac'] at heq
  rw [atom_residue_eq_distinguished_add_companion,
    atom_residue_eq_distinguished_add_companion] at heq
  have hcomp : reciprocalResidue g.companionDenominator
      - reciprocalResidue g'.companionDenominator ∈ lowerPrimePowerStage p :=
    AddSubgroup.sub_mem _ (companion_mem_lowerPrimePowerStage g hb)
      (companion_mem_lowerPrimePowerStage g' hb')
  have hdist : reciprocalResidue (g.distinguishedDenominator hppos)
      - reciprocalResidue (g'.distinguishedDenominator hppos)
        ∈ lowerPrimePowerStage p := by
    have hsub := AddSubgroup.sub_mem _ heq hcomp
    have hrw : (reciprocalResidue (g.distinguishedDenominator hppos)
          + reciprocalResidue g.companionDenominator
        - (reciprocalResidue (g'.distinguishedDenominator hppos)
          + reciprocalResidue g'.companionDenominator))
        - (reciprocalResidue g.companionDenominator
          - reciprocalResidue g'.companionDenominator)
        = reciprocalResidue (g.distinguishedDenominator hppos)
          - reciprocalResidue (g'.distinguishedDenominator hppos) := by
      abel
    rwa [hrw] at hsub
  have hk := coefficient_pos_lt w g.sign
  have hk' := coefficient_pos_lt w' g'.sign
  exact reciprocalResidue_sub_notMem_lower hp hk.1 hk'.1
    (lt_trans hk.2 hb) (lt_trans hk'.2 hb') hne _ _ hdist

end SignedInverse
end Erdos289
