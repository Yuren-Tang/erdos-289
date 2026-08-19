module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PresentationComposition
public import Erdos289.NeutralConstruction
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Cofinal composition of paired deformations

Both faces of a later deformation are placed beyond the joint footprint of the
earlier pair.  Union then realizes addition of values and grades without
exposing any coordinate-selection mechanism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

def pairFootprint (S T : Support) : Support := S ∪ T

theorem crossSeparated_of_subset_left
    {R S T : Support} {m : ℕ} (hRS : R ⊆ S)
    (h : S.CrossSeparated T m) : R.CrossSeparated T m := by
  intro x hx y hy
  exact h x (hRS hx) y hy

/-! ### Composing a support with a compatible one

The second support has only to be *compatible* with a footprint containing the
first: disjoint from it and separated from it.  Remoteness beyond the footprint
is one way of achieving that, and the `Beyond` corollaries below record it, but
the composition itself never needs more than compatibility.
-/

theorem admissible_union_of_pair
    {L : Set ℕ} (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hS : S.Admissible L c)
    (hV : V.Admissible L (constraintAvoiding c F)) :
    (S ∪ V).Admissible L c := by
  have hfull := crossSeparated_of_avoids_avoiding c hV.2.1
  have hcross := crossSeparated_of_subset_left hSF hfull
  exact Support.admissible_union
    (crossSeparated_graphDisjoint
      (crossSeparated_mono hcross (Nat.le_max_left 1 c.separation)))
    (crossSeparated_mono hcross (Nat.le_max_right 1 c.separation))
    hS (admissible_of_admissible_avoiding c hV)

theorem value_union_of_pair
    (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hV : V.Avoids (constraintAvoiding c F)) :
    (S ∪ V).value = S.value + V.value := by
  have hfull := crossSeparated_of_avoids_avoiding c hV
  have hcross := crossSeparated_of_subset_left hSF hfull
  exact Support.value_union (crossSeparated_graphDisjoint
    (crossSeparated_mono hcross (Nat.le_max_left 1 c.separation))).1

theorem grade_union_of_pair
    (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hV : V.Avoids (constraintAvoiding c F)) :
    (S ∪ V).grade = S.grade + V.grade := by
  have hfull := crossSeparated_of_avoids_avoiding c hV
  have hcross := crossSeparated_of_subset_left hSF hfull
  exact Support.grade_union_of_graphDisjoint (crossSeparated_graphDisjoint
    (crossSeparated_mono hcross (Nat.le_max_left 1 c.separation)))

theorem admissible_union_of_pairBeyond
    {L : Set ℕ} (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hS : S.Admissible L c)
    (hV : V.Admissible L (constraintBeyond c F)) :
    (S ∪ V).Admissible L c :=
  admissible_union_of_pair c hSF hS (admissible_avoiding_of_admissible_beyond c hV)

theorem value_union_of_pairBeyond
    (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hV : V.Avoids (constraintBeyond c F)) :
    (S ∪ V).value = S.value + V.value :=
  value_union_of_pair c hSF (avoids_avoiding_of_avoids_beyond c hV)

theorem grade_union_of_pairBeyond
    (c : PhysicalConstraint) {S F V : Support}
    (hSF : S ⊆ F)
    (hV : V.Avoids (constraintBeyond c F)) :
    (S ∪ V).grade = S.grade + V.grade :=
  grade_union_of_pair c hSF (avoids_avoiding_of_avoids_beyond c hV)

/-- Iterating the neutral grade-one fibre gives every finite neutral grade shift. -/
theorem neutralGradePoint
    (hN : RemoteLightNeutralGradeOne)
    (k : ℕ) (c : PhysicalConstraint) (ε : ℚ) (hε : 0 < ε) :
    Nonempty (NeutralGradePoint k c ε) := by
  induction k generalizing c ε with
  | zero =>
      exact ⟨{
        lower := ∅
        upper := ∅
        lower_admissible := by
          simp [Support.Admissible, Support.HasBlockSizes,
            Support.Avoids, Support.Separated]
        upper_admissible := by
          simp [Support.Admissible, Support.HasBlockSizes,
            Support.Avoids, Support.Separated]
        value_eq := by simp
        grade_eq := by simp [Support.grade]
        lower_value_lt := by simpa using hε }⟩
  | succ k ih =>
      have hhalf : 0 < ε / 2 := by linarith
      obtain ⟨x⟩ := ih c (ε / 2) hhalf
      let footprint := pairFootprint x.lower x.upper
      obtain ⟨y⟩ := hN (constraintBeyond c footprint) (ε / 2) hhalf
      refine ⟨{
        lower := x.lower ∪ y.lower
        upper := x.upper ∪ y.upper
        lower_admissible := admissible_union_of_pairBeyond c
          (F := footprint)
          (by intro z hz; exact Finset.mem_union_left _ hz)
          x.lower_admissible y.lower_admissible
        upper_admissible := admissible_union_of_pairBeyond c
          (S := x.upper) (F := footprint)
          (by intro z hz; exact Finset.mem_union_right _ hz)
          x.upper_admissible y.upper_admissible
        value_eq := ?_
        grade_eq := ?_
        lower_value_lt := ?_ }⟩
      · rw [value_union_of_pairBeyond c
            (F := footprint)
            (by intro z hz; exact Finset.mem_union_right _ hz)
            y.upper_admissible.2.1,
          value_union_of_pairBeyond c
            (F := footprint)
            (by intro z hz; exact Finset.mem_union_left _ hz)
            y.lower_admissible.2.1,
          x.value_eq, y.value_eq]
      · rw [grade_union_of_pairBeyond c
            (F := footprint)
            (by intro z hz; exact Finset.mem_union_right _ hz)
            y.upper_admissible.2.1,
          grade_union_of_pairBeyond c
            (F := footprint)
            (by intro z hz; exact Finset.mem_union_left _ hz)
            y.lower_admissible.2.1,
          x.grade_eq, y.grade_eq]
        omega
      · rw [value_union_of_pairBeyond c
            (F := footprint)
            (by intro z hz; exact Finset.mem_union_left _ hz)
            y.lower_admissible.2.1]
        linarith [x.lower_value_lt, y.value_lt]

end Erdos289
