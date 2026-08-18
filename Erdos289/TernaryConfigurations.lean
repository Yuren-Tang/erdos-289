module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryConfigurations
public import Erdos289.TernaryBlocks

@[expose] public section

/-!
# Finite configurations of remote ternary blocks

As for binary configurations, the placement predicate records exactly the
physical facts consumed downstream.  Polynomial or Egyptian coordinates used
to choose starts do not occur in this interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- Union of the canonical ternary blocks at the prescribed starts. -/
def ternaryConfiguration (starts : Finset Denominator) : Support :=
  starts.biUnion ternaryBlock

@[simp]
theorem ternaryConfiguration_empty : ternaryConfiguration ∅ = ∅ := by
  simp [ternaryConfiguration]

theorem ternaryConfiguration_insert {a : Denominator} {starts : Finset Denominator} :
    ternaryConfiguration (insert a starts) =
      ternaryBlock a ∪ ternaryConfiguration starts := by
  simp [ternaryConfiguration]

/-- Remote obstacle avoidance and pairwise physical separation of ternary atoms. -/
def TernaryPlacement (c : PhysicalConstraint) (starts : Finset Denominator) : Prop :=
  (∀ a ∈ starts, c.obstacleCutoff < a.1) ∧
  ∀ a ∈ starts, ∀ b ∈ starts, a ≠ b →
    (ternaryBlock a).CrossSeparated (ternaryBlock b) (max 1 c.separation)

/--
A start-distance margin survives expansion to length-three intervals: the
diameter of the pattern is two, so `m + 2` apart at the starts is `m` apart at
the blocks.  The `2` is the diameter, not a margin.
-/
theorem ternaryBlock_crossSeparated_of_dist
    {a b : Denominator} {m : ℕ}
    (h : m + 2 < Nat.dist a.1 b.1) :
    (ternaryBlock a).CrossSeparated (ternaryBlock b) m :=
  Support.crossSeparated_of_window (ternaryBlock_window a) (ternaryBlock_window b) h
theorem ternaryBlock_graphDisjoint_configuration
    (c : PhysicalConstraint) {a : Denominator} {starts : Finset Denominator}
    (ha : a ∉ starts) (hplace : TernaryPlacement c (insert a starts)) :
    (ternaryBlock a).GraphDisjoint (ternaryConfiguration starts) := by
  apply crossSeparated_graphDisjoint
  intro x hx y hy
  rcases Finset.mem_biUnion.mp hy with ⟨b, hb, hyb⟩
  exact lt_of_le_of_lt (Nat.le_max_left 1 c.separation)
    (hplace.2 a (by simp) b (by simp [hb]) (by
      intro hab
      subst b
      exact ha hb) x hx y hyb)

theorem ternaryConfiguration_admissible
    (c : PhysicalConstraint) (starts : Finset Denominator)
    (hplace : TernaryPlacement c starts) :
    (ternaryConfiguration starts).Admissible smallBlockSizes c := by
  classical
  induction starts using Finset.induction with
  | empty =>
      simp [ternaryConfiguration, Support.Admissible, Support.HasBlockSizes,
        Support.Avoids, Support.Separated]
  | @insert a starts ha ih =>
      rw [ternaryConfiguration_insert]
      apply Support.admissible_union
      · exact ternaryBlock_graphDisjoint_configuration c ha hplace
      · intro x hx y hy
        rcases Finset.mem_biUnion.mp hy with ⟨b, hb, hyb⟩
        exact lt_of_le_of_lt (Nat.le_max_right 1 c.separation)
          (hplace.2 a (by simp) b (by simp [hb]) (by
            intro hab
            subst b
            exact ha hb) x hx y hyb)
      · exact ternaryBlock_admissible c a (hplace.1 a (by simp))
      · apply ih
        constructor
        · intro b hb
          exact hplace.1 b (by simp [hb])
        · intro b hb d hd hbd
          exact hplace.2 b (by simp [hb]) d (by simp [hd]) hbd

theorem ternaryConfiguration_grade
    (c : PhysicalConstraint) (starts : Finset Denominator)
    (hplace : TernaryPlacement c starts) :
    (ternaryConfiguration starts).grade = starts.card := by
  classical
  induction starts using Finset.induction with
  | empty => simp [ternaryConfiguration, Support.grade]
  | @insert a starts ha ih =>
      rw [ternaryConfiguration_insert]
      rw [Support.grade_union_of_graphDisjoint
        (ternaryBlock_graphDisjoint_configuration c ha hplace)]
      rw [ternaryBlock_grade, ih]
      · simp [ha, Nat.add_comm]
      · constructor
        · intro b hb
          exact hplace.1 b (by simp [hb])
        · intro b hb d hd hbd
          exact hplace.2 b (by simp [hb]) d (by simp [hd]) hbd

theorem ternaryConfiguration_value
    (c : PhysicalConstraint) (starts : Finset Denominator)
    (hplace : TernaryPlacement c starts) :
    (ternaryConfiguration starts).value =
      ∑ a ∈ starts, (reciprocal a + binaryBlockMass (a + 1)) := by
  classical
  induction starts using Finset.induction with
  | empty => simp [ternaryConfiguration]
  | @insert a starts ha ih =>
      rw [ternaryConfiguration_insert]
      rw [Support.value_union
        (ternaryBlock_graphDisjoint_configuration c ha hplace).1]
      rw [ternaryBlock_value, ih]
      · simp [ha]
      · constructor
        · intro b hb
          exact hplace.1 b (by simp [hb])
        · intro b hb d hd hbd
          exact hplace.2 b (by simp [hb]) d (by simp [hd]) hbd

end Erdos289
