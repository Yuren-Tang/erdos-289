import Reciprocal.State
import Universal.Target.Centering

import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Centered reciprocal geometry

The reciprocal specialization of marked-family centering: the grading group is
`Γ = ℚ`, the mark is `τ = 1`, and the centered target is `A = ℚ/ℤ`.  The
centered residue is the composite of the reciprocal value with the canonical
quotient map, and the exact fibre is the locus where the reciprocal value is
one.
-/

open scoped BigOperators

namespace Erdos289

universe v

/-- The reciprocal marking: the one-point marking of `Γ = ℚ` at `τ = 1`. -/
def reciprocalMarking : Marking ℚ := singletonMarking (1 : ℚ)

/-- The centered residue group `A = ℚ/ℤ`. -/
abbrev CenteredResidueGroup := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- The canonical quotient map `q_τ : ℚ → A`. -/
def centeredResidueQuotient : ℚ →+ CenteredResidueGroup :=
  QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))

/-- The unique mark of the reciprocal marking. -/
private def reciprocalMark : reciprocalMarking.left := PUnit.unit

private theorem markingFreeMap_reciprocal_of (x : reciprocalMarking.left) :
    markingFreeMap reciprocalMarking (FreeAbelianGroup.of x) = 1 := by
  show (FreeAbelianGroup.lift reciprocalMarking.hom) (FreeAbelianGroup.of x) = 1
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

/-- The marks of the reciprocal marking generate exactly the integers. -/
theorem markingFreeMap_reciprocal_range :
    (markingFreeMap reciprocalMarking).range = AddSubgroup.zmultiples (1 : ℚ) := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    induction w using FreeAbelianGroup.induction_on with
    | zero =>
        rw [map_zero]
        exact AddSubgroup.zero_mem _
    | of x =>
        rw [markingFreeMap_reciprocal_of]
        exact AddSubgroup.mem_zmultiples _
    | neg x ih =>
        rw [map_neg]
        exact AddSubgroup.neg_mem _ ih
    | add x y ihx ihy =>
        rw [map_add]
        exact AddSubgroup.add_mem _ ihx ihy
  · rintro q hq
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
    refine ⟨k • FreeAbelianGroup.of reciprocalMark, ?_⟩
    rw [map_zsmul, markingFreeMap_reciprocal_of]

private theorem range_le_zmultiples :
    (markingFreeMap reciprocalMarking).range ≤
      (AddSubgroup.zmultiples (1 : ℚ)).comap (AddMonoidHom.id ℚ) := by
  rw [AddSubgroup.comap_id, markingFreeMap_reciprocal_range]

private theorem zmultiples_le_range :
    AddSubgroup.zmultiples (1 : ℚ) ≤
      (markingFreeMap reciprocalMarking).range.comap (AddMonoidHom.id ℚ) := by
  rw [AddSubgroup.comap_id, markingFreeMap_reciprocal_range]

/-- The canonical identification of the centered target of the reciprocal
marking with `ℚ/ℤ`. -/
def centeredResidueEquiv :
    CenteredMarking reciprocalMarking ≃+ CenteredResidueGroup where
  toFun := QuotientAddGroup.map _ _ (AddMonoidHom.id ℚ) range_le_zmultiples
  invFun := QuotientAddGroup.map _ _ (AddMonoidHom.id ℚ) zmultiples_le_range
  left_inv z := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    rfl
  right_inv z := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ z
    rfl
  map_add' x y := map_add _ x y

@[simp]
theorem centeredResidueEquiv_markingQuotient (x : ℚ) :
    centeredResidueEquiv (markingQuotient reciprocalMarking x) =
      centeredResidueQuotient x :=
  rfl

@[simp]
theorem centeredResidueEquiv_symm_quotient (x : ℚ) :
    centeredResidueEquiv.symm (centeredResidueQuotient x) =
      markingQuotient reciprocalMarking x :=
  rfl

/-- The centered residue `W̄ = q_τ ∘ W : C → A`. -/
noncomputable def centeredResidue (S : E289State) : CenteredResidueGroup :=
  centeredResidueQuotient (reciprocalValue S)

/-- The exact fibre `C₁ = W⁻¹(1)`. -/
def ExactFibre : Set E289State := {S | reciprocalValue S = 1}

@[simp]
theorem mem_exactFibre_iff (S : E289State) :
    S ∈ ExactFibre ↔ reciprocalValue S = 1 :=
  Iff.rfl

/-- Residue/value compatibility: the centered residue vanishes exactly on
integral reciprocal values. -/
theorem centeredResidue_eq_zero_iff (S : E289State) :
    centeredResidue S = 0 ↔ ∃ k : ℤ, reciprocalValue S = (k : ℚ) := by
  rw [centeredResidue, centeredResidueQuotient, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, zsmul_eq_mul, mul_one]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk, zsmul_eq_mul, mul_one]⟩

/-- Every exact state has vanishing centered residue. -/
theorem centeredResidue_of_mem_exactFibre {S : E289State} (hS : S ∈ ExactFibre) :
    centeredResidue S = 0 :=
  (centeredResidue_eq_zero_iff S).2
    ⟨1, ((mem_exactFibre_iff S).1 hS).trans Int.cast_one.symm⟩

/-- The centered residue is additive on direct compatibility. -/
theorem centeredResidue_naryUnion {I : Type v} [Fintype I] {S : I → E289State}
    (hS : NaryCompatible S) :
    centeredResidue (naryUnion S hS) = ∑ i, centeredResidue (S i) := by
  rw [centeredResidue, reciprocalValue_naryUnion hS, map_sum]
  rfl

end Erdos289
