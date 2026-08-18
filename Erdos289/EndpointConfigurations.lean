module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PresentationComposition
public import Erdos289.TernaryConfigurations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Physical endpoint configurations from reciprocal presentations

A separated coefficient-one presentation canonically indexes two configuration
faces: shifted binary intervals and their ternary endpoint extensions.  This
module proves the physical placement facts; it does not choose presentation
coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

def shiftOne (a : Denominator) : Denominator := a + 1

theorem shiftOne_injective : Function.Injective shiftOne := by
  intro a b h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  have ha : (shiftOne a).1 = a.1 + 1 := PNat.add_coe a 1
  have hb : (shiftOne b).1 = b.1 + 1 := PNat.add_coe b 1
  omega

def endpointBinaryStarts (S : Support) : Finset Denominator :=
  S.image shiftOne

/--
The constraint requested before expanding starts to length-three intervals.

Both data are forced.  The obstacle is exactly the obstacle cutoff of `c`,
because a block starting beyond that cutoff already avoids `c`.  The separation
is the effective margin of `c` inflated by the *diameter* of the pattern being
placed, which for a length-three interval is two.
-/
def endpointConstraint (c : PhysicalConstraint) : PhysicalConstraint where
  obstacle := denominatorPrefix c.obstacleCutoff
  separation := max 1 c.separation + 2

@[simp] theorem endpointConstraint_separation (c : PhysicalConstraint) :
    (endpointConstraint c).separation = max 1 c.separation + 2 := rfl

theorem presentation_start_remote
    {q : ℚ} {c : PhysicalConstraint}
    (w : RationalPresentation q (endpointConstraint c))
    {a : Denominator} (ha : a ∈ w.support) :
    c.obstacleCutoff < a.1 := by
  have hnot : a ∉ (endpointConstraint c).obstacle := by
    intro hobs
    exact (Finset.disjoint_left.mp w.avoids ha) hobs
  simp only [endpointConstraint, mem_denominatorPrefix] at hnot
  omega

theorem presentation_ternaryPlacement
    {q : ℚ} {c : PhysicalConstraint}
    (w : RationalPresentation q (endpointConstraint c)) :
    TernaryPlacement c w.support := by
  constructor
  · intro a ha
    exact presentation_start_remote w ha
  · intro a ha b hb hab
    refine ternaryBlock_crossSeparated_of_dist ?_
    have hsep := w.pointSeparated a ha b hb hab
    rwa [endpointConstraint_separation] at hsep

theorem binaryBlock_shift_subset_ternaryBlock (a : Denominator) :
    binaryBlock (shiftOne a) ⊆ ternaryBlock a := by
  intro x hx
  rcases mem_binaryBlock.mp hx with hx | hx
  · exact mem_ternaryBlock.mpr (Or.inr (Or.inl hx))
  · have h12 : shiftOne a + 1 = a + 2 := by
      apply Subtype.ext
      have hs : (shiftOne a).1 = a.1 + 1 := PNat.add_coe a 1
      have hs1 : (shiftOne a + 1).1 = (shiftOne a).1 + 1 :=
        PNat.add_coe (shiftOne a) 1
      have h2 : (a + 2).1 = a.1 + 2 := PNat.add_coe a 2
      omega
    exact mem_ternaryBlock.mpr (Or.inr (Or.inr (hx.trans h12)))

theorem presentation_binaryPlacement
    {q : ℚ} {c : PhysicalConstraint}
    (w : RationalPresentation q (endpointConstraint c)) :
    BinaryPlacement c (endpointBinaryStarts w.support) := by
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    have hremote := presentation_start_remote w ha
    have hs : (shiftOne a).1 = a.1 + 1 := PNat.add_coe a 1
    omega
  · intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => hxy (congrArg shiftOne h)
    have hsep := w.pointSeparated a ha b hb hab
    rw [endpointConstraint_separation] at hsep
    have hternary : (ternaryBlock a).CrossSeparated (ternaryBlock b)
        (max 1 c.separation) := ternaryBlock_crossSeparated_of_dist hsep
    intro u hu v hv
    exact hternary u (binaryBlock_shift_subset_ternaryBlock a hu)
      v (binaryBlock_shift_subset_ternaryBlock b hv)

theorem endpointBinaryStarts_card (S : Support) :
    (endpointBinaryStarts S).card = S.card := by
  exact Finset.card_image_of_injective S shiftOne_injective

/-- A remote reciprocal presentation gives a legal same-grade endpoint deformation. -/
def RationalPresentation.endpointDeformation
    {q : ℚ} {c : PhysicalConstraint}
    (w : RationalPresentation q (endpointConstraint c)) :
    SameGradeDeformation q c where
  lower := binaryConfiguration (endpointBinaryStarts w.support)
  upper := ternaryConfiguration w.support
  lower_admissible := binaryConfiguration_admissible c _
    (presentation_binaryPlacement w)
  upper_admissible := ternaryConfiguration_admissible c _
    (presentation_ternaryPlacement w)
  value_eq := by
    rw [ternaryConfiguration_value c _ (presentation_ternaryPlacement w),
      binaryConfiguration_value c _ (presentation_binaryPlacement w)]
    have hsum :
        ∑ x ∈ endpointBinaryStarts w.support, binaryBlockMass x =
          ∑ a ∈ w.support, binaryBlockMass (shiftOne a) := by
      unfold endpointBinaryStarts
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact shiftOne_injective hab
    rw [hsum]
    simp only [shiftOne]
    rw [Finset.sum_add_distrib]
    have hvalue : ∑ a ∈ w.support, reciprocal a = q := by
      simpa [Support.value] using w.value_eq
    rw [hvalue]
    ac_rfl
  grade_eq := by
    rw [ternaryConfiguration_grade c _ (presentation_ternaryPlacement w),
      binaryConfiguration_grade c _ (presentation_binaryPlacement w),
      endpointBinaryStarts_card]

theorem shiftedBinaryBlockMass_lt_two_mul_reciprocal (a : Denominator) :
    binaryBlockMass (shiftOne a) < 2 * reciprocal a := by
  apply (binaryBlockMass_lt_two_div (shiftOne a)).trans
  have ha : (0 : ℚ) < (a.1 : ℚ) := by exact_mod_cast a.2
  have ha1 : (0 : ℚ) < (a.1 : ℚ) + 1 := by positivity
  unfold reciprocal
  rw [show (shiftOne a).1 = a.1 + 1 by exact PNat.add_coe a 1,
    Nat.cast_add, Nat.cast_one]
  rw [show 2 * (1 / (a.1 : ℚ)) = 2 / (a.1 : ℚ) by ring]
  apply (div_lt_div_iff₀ ha1 ha).2
  nlinarith

/-- The lower resource of an endpoint deformation is less than twice its increment. -/
theorem RationalPresentation.endpointDeformation_lower_lt_two_mul
    {q : ℚ} {c : PhysicalConstraint} (hq : 0 < q)
    (w : RationalPresentation q (endpointConstraint c)) :
    w.endpointDeformation.lower.value < 2 * q := by
  have hne : w.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hv := w.value_eq
    rw [h] at hv
    simp [Support.value] at hv
    linarith
  change (binaryConfiguration (endpointBinaryStarts w.support)).value < 2 * q
  rw [binaryConfiguration_value c _ (presentation_binaryPlacement w)]
  unfold endpointBinaryStarts
  rw [Finset.sum_image]
  · calc
      ∑ a ∈ w.support, binaryBlockMass (shiftOne a) <
          ∑ a ∈ w.support, 2 * reciprocal a :=
        Finset.sum_lt_sum_of_nonempty hne fun a _ =>
          shiftedBinaryBlockMass_lt_two_mul_reciprocal a
      _ = 2 * q := by
        rw [← Finset.mul_sum]
        congr 1
        simpa [Support.value] using w.value_eq
  · intro a _ b _ hab
    exact shiftOne_injective hab

/-- Leaf E already implies existence of every endpoint-deformation fibre. -/
theorem endpointDeformation_of_unitFractionRefinement
    (hE : UnitFractionRefinementCofinality)
    (q : ℚ) (hq : 0 < q) (c : PhysicalConstraint) :
    Nonempty (SameGradeDeformation q c) := by
  obtain ⟨w⟩ := rationalPresentation_of_pos hE q hq (endpointConstraint c)
  exact ⟨w.endpointDeformation⟩

end Erdos289
