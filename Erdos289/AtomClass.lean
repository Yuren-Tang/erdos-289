module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.SignedInverseAtom
public import Erdos289.SimpleFibre
public import Erdos289.StageProfile

@[expose] public section

/-!
# The simple-fibre class of a signed-inverse atom

At a prime-power current `Q = p ^ e` the class of an oriented atom in the
simple fibre is pinned by one equation:

  `k • class = generator`,

where `k` is the atom's current coefficient and the generator is the class of
`1/Q`.  The reason is exact rather than approximate: the atom's residue is its
distinguished reciprocal `1/(Q k)` plus a companion lying in the lower stage,
and `k · (1/(Q k)) = 1/Q` on the nose.

Since the fibre has prime order `p` and the coefficient is a unit modulo `p`,
that equation determines the class, and two atoms share a class exactly when
their coefficients agree modulo `p`.  This is the arithmetic description of the
row's image in the fibre, uniform in the exponent: at a prime current it
specializes to the injectivity used by the fold, and at a proper prime power it
is what identifies the stocks the cyclic mechanism needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-- Scaling a reciprocal by its cofactor: `k · (1/(Q k)) = 1/Q`. -/
theorem nsmul_reciprocalResidue_mul {Q k : ℕ} (hQ : 0 < Q) (hk : 0 < k) :
    k • reciprocalResidue ⟨Q * k, Nat.mul_pos hQ hk⟩ = reciprocalResidue ⟨Q, hQ⟩ := by
  unfold reciprocalResidue
  rw [← map_nsmul]
  congr 1
  have hQ0 : ((Q : ℚ)) ≠ 0 := by exact_mod_cast hQ.ne'
  have hk0 : ((k : ℚ)) ≠ 0 := by exact_mod_cast hk.ne'
  show (k : ℕ) • reciprocal ⟨Q * k, Nat.mul_pos hQ hk⟩ = reciprocal ⟨Q, hQ⟩
  unfold reciprocal
  rw [nsmul_eq_mul]
  push_cast
  field_simp

/--
The defining equation of an atom's class: the coefficient scales it to the
canonical generator of the fibre.
-/
theorem coefficient_nsmul_atom_simpleFibreClass
    {Q b p : ℕ} {w : ComplementaryPair Q b} (g : GoodOrientation p w)
    (hQpos : 0 < Q) (hbQ : b < Q)
    (hfac : (g.atom hQpos).FactorsThroughPrimePowerStage Q) :
    (w.coefficient g.sign) • ((g.atom hQpos).simpleFibreClass hfac)
      = primePowerGenerator Q hQpos := by
  classical
  set k := w.coefficient g.sign with hk
  have hkpos : 0 < k := (coefficient_pos_lt w g.sign).1
  have hres := atom_residue_eq_distinguished_add_companion g hQpos
  have hdist : (g.distinguishedDenominator hQpos) = ⟨Q * k, Nat.mul_pos hQpos hkpos⟩ := rfl
  -- the scaled residue differs from `1/Q` by a scaled companion, which is lower
  have hlower : k • (g.atom hQpos).residue - reciprocalResidue ⟨Q, hQpos⟩
      ∈ lowerPrimePowerStage Q := by
    have hcomp : k • reciprocalResidue g.companionDenominator ∈ lowerPrimePowerStage Q :=
      AddSubgroup.nsmul_mem _ (companion_mem_lowerPrimePowerStage g hbQ) k
    have hsplit : k • (g.atom hQpos).residue
        = reciprocalResidue ⟨Q, hQpos⟩ + k • reciprocalResidue g.companionDenominator := by
      rw [hres, smul_add, hdist, nsmul_reciprocalResidue_mul hQpos hkpos]
    rw [hsplit]
    simpa using hcomp
  have hmem : k • (g.atom hQpos).residue ∈ primePowerStage Q :=
    AddSubgroup.nsmul_mem _ hfac k
  have hgen : reciprocalResidue ⟨Q, hQpos⟩ ∈ primePowerStage Q :=
    annihilatorStage_le Q (reciprocalResidue_mem_annihilatorStage ⟨Q, hQpos⟩)
  have hclass : (QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q)
        (⟨k • (g.atom hQpos).residue, hmem⟩ : primePowerStage Q))
      = QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q)
        (⟨reciprocalResidue ⟨Q, hQpos⟩, hgen⟩ : primePowerStage Q) :=
    (simpleFibre_mk_eq_iff_sub_mem hmem hgen).2 hlower
  calc k • ((g.atom hQpos).simpleFibreClass hfac)
      = QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q)
          (⟨k • (g.atom hQpos).residue, hmem⟩ : primePowerStage Q) := by
        rw [Support.simpleFibreClass, ← map_nsmul]
        rfl
    _ = _ := hclass

/--
Two oriented atoms of the same current share a simple-fibre class exactly when
their coefficients agree modulo `p`.
-/
theorem atom_simpleFibreClass_eq_iff
    {Q b b' p e : ℕ} {w : ComplementaryPair Q b} {w' : ComplementaryPair Q b'}
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (g : GoodOrientation p w) (g' : GoodOrientation p w')
    (hQpos : 0 < Q) (hbQ : b < Q) (hb'Q : b' < Q)
    (hfac : (g.atom hQpos).FactorsThroughPrimePowerStage Q)
    (hfac' : (g'.atom hQpos).FactorsThroughPrimePowerStage Q) :
    (g.atom hQpos).simpleFibreClass hfac = (g'.atom hQpos).simpleFibreClass hfac'
      ↔ ((w.coefficient g.sign : ZMod p) = (w'.coefficient g'.sign : ZMod p)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set φ := primePowerSimpleFibreAddEquiv hp he hQ with hφ
  set y := (g.atom hQpos).simpleFibreClass hfac with hy
  set y' := (g'.atom hQpos).simpleFibreClass hfac' with hy'
  set k := w.coefficient g.sign with hk
  set k' := w'.coefficient g'.sign with hk'
  have hgen : φ (primePowerGenerator Q hQpos) ≠ 0 := by
    intro hzero
    exact absurd (φ.injective (by simpa using hzero))
      (by simpa using primePowerGenerator_ne_zero hp he hQ)
  have hEq : ∀ {c : ℕ} {z : PrimePowerSimpleFibre Q},
      c • z = primePowerGenerator Q hQpos →
        (c : ZMod p) * φ z = φ (primePowerGenerator Q hQpos) := by
    intro c z hcz
    rw [← hcz, map_nsmul, nsmul_eq_mul]
  have h1 := hEq (coefficient_nsmul_atom_simpleFibreClass g hQpos hbQ hfac)
  have h2 := hEq (coefficient_nsmul_atom_simpleFibreClass g' hQpos hb'Q hfac')
  constructor
  · intro heq
    have hyy : φ y = φ y' := by rw [heq]
    have : (k : ZMod p) * φ y' = (k' : ZMod p) * φ y' := by
      calc (k : ZMod p) * φ y' = (k : ZMod p) * φ y := by rw [hyy]
        _ = φ (primePowerGenerator Q hQpos) := h1
        _ = (k' : ZMod p) * φ y' := h2.symm
    have hy'0 : φ y' ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at h2
      exact hgen h2.symm
    exact mul_right_cancel₀ hy'0 this
  · intro hkk
    refine φ.injective ?_
    have hy0 : φ y ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at h1
      exact hgen h1.symm
    have hk0 : (k : ZMod p) ≠ 0 := by
      intro hzero
      have : (k : ZMod p) * φ y = 0 := by rw [hzero, zero_mul]
      exact hgen (by rw [← h1, this])
    have hmul : (k : ZMod p) * φ y = (k : ZMod p) * φ y' := by
      calc (k : ZMod p) * φ y = φ (primePowerGenerator Q hQpos) := h1
        _ = (k' : ZMod p) * φ y' := h2.symm
        _ = (k : ZMod p) * φ y' := by rw [hkk]
    exact mul_left_cancel₀ hk0 hmul

end SignedInverse
end Erdos289
