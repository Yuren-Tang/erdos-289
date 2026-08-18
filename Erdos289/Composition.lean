module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PoolComposition
public import Erdos289.DeformationComposition
public import Erdos289.Selector

@[expose] public section

/-!
# Assembling an exact witness from a compatible pool

`Erdos289/PoolComposition.lean` proves that admissibility, exact value and
connected-component grade are all additive over a pairwise-compatible finite
pool.  Centering is a group homomorphism on values, so the centered residue is
additive too, and the three additivity statements together turn a pool into a
saturation witness as soon as the selector conditions hold: total value in the
open interval `(0, 2)` and total centered residue zero.

This is the point where the descent's last step becomes a finite computation:
the arithmetic layers have to supply pools whose total residue vanishes and
whose total value stays inside the selector interval, and nothing else.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/-- Exact reciprocal value is nonnegative: it is a sum of reciprocals. -/
theorem Support.value_nonneg (S : Support) : 0 ≤ S.value := by
  show (0 : ℚ) ≤ ∑ n ∈ S, reciprocal n
  refine Finset.sum_nonneg fun n _ => ?_
  have hn : (0 : ℚ) < (n.1 : ℚ) := by exact_mod_cast n.2
  show (0 : ℚ) ≤ 1 / (n.1 : ℚ)
  exact div_nonneg zero_le_one hn.le

/-- Centering is additive, so the residue of a compatible pool is the sum. -/
theorem aggregateSupport_residue
    {c : PhysicalConstraint} {A : Finset Support}
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c) :
    (aggregateSupport A).residue = ∑ S ∈ A, S.residue := by
  have hval := aggregateSupport_value hpair
  change AffineCorrection.CenteredValue.mk (1 : ℚ) (aggregateSupport A).value = _
  rw [hval, map_sum]
  rfl

/--
The selector applied to a compatible pool: a finite pairwise-compatible family
of admissible atoms whose exact values sum into `(0, 2)` and whose centered
residues cancel is a saturation witness at the sum of the grades.
-/
noncomputable def saturationWitness_of_pool
    {c : PhysicalConstraint} {A : Finset Support}
    (hadm : ∀ S ∈ A, S.Admissible smallBlockSizes c)
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c)
    (hpos : 0 < ∑ S ∈ A, S.value) (hlt : ∑ S ∈ A, S.value < 2)
    (hres : ∑ S ∈ A, S.residue = 0) :
    SaturationWitness 1 c (∑ S ∈ A, S.grade) :=
  saturationWitness_of_residue_zero
    (aggregateSupport_admissible hadm hpair)
    (aggregateSupport_grade hpair)
    (by rw [aggregateSupport_value hpair]; exact hpos)
    (by rw [aggregateSupport_value hpair]; exact hlt)
    (by rw [aggregateSupport_residue hpair]; exact hres)

/-- Centering is additive over a `beyond` composition of two supports. -/
theorem residue_union_of_pairBeyond
    (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F) (hV : V.Avoids (constraintBeyond c F)) :
    (S ∪ V).residue = S.residue + V.residue := by
  have hval := value_union_of_pairBeyond c hSF hV
  change AffineCorrection.CenteredValue.mk (1 : ℚ) (S ∪ V).value = _
  rw [hval, map_add]
  rfl

/--
Two-stage form of the same statement: a prefix and a tail placed beyond its
footprint compose to a saturation witness when their values and residues meet
the selector conditions.
-/
noncomputable def saturationWitness_of_pairBeyond
    (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hS : S.Admissible smallBlockSizes c)
    (hV : V.Admissible smallBlockSizes (constraintBeyond c F))
    (hpos : 0 < S.value + V.value) (hlt : S.value + V.value < 2)
    (hres : S.residue + V.residue = 0) :
    SaturationWitness 1 c (S.grade + V.grade) :=
  saturationWitness_of_residue_zero
    (admissible_union_of_pairBeyond c hSF hS hV)
    (grade_union_of_pairBeyond c hSF hV.2.1)
    (by rw [value_union_of_pairBeyond c hSF hV.2.1]; exact hpos)
    (by rw [value_union_of_pairBeyond c hSF hV.2.1]; exact hlt)
    (by rw [residue_union_of_pairBeyond c hSF hV.2.1]; exact hres)

/--
Cofinite saturation at the unit target from a stagewise supply of compatible
pools.  This is the exact interface the quantitative arithmetic layers have to
meet; see `ROADMAP.md`.
-/
theorem cofiniteSaturation_one_of_pools
    {c : PhysicalConstraint} {N : ℕ}
    (h : ∀ k, N ≤ k → ∃ A : Finset Support,
      (∀ S ∈ A, S.Admissible smallBlockSizes c) ∧
      (A : Set Support).Pairwise (fun S T ↦ S.CompatibleFor T c) ∧
      ∑ S ∈ A, S.grade = k ∧
      0 < ∑ S ∈ A, S.value ∧ ∑ S ∈ A, S.value < 2 ∧
      ∑ S ∈ A, S.residue = 0) :
    CofiniteSaturation 1 c := by
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨A, hadm, hpair, hgrade, hpos, hlt, hres⟩ := h k hk
  exact ⟨hgrade ▸ saturationWitness_of_pool hadm hpair hpos hlt hres⟩

end Erdos289
