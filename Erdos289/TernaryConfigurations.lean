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

/-- A start-distance margin survives expansion to two-step path intervals. -/
theorem ternaryBlock_crossSeparated_of_dist
    {a b : Denominator} {m : ℕ}
    (h : m + 4 < Nat.dist a.1 b.1) :
    (ternaryBlock a).CrossSeparated (ternaryBlock b) m := by
  intro x hx y hy
  have hxlo : a.1 ≤ x.1 := by
    rcases mem_ternaryBlock.mp hx with rfl | rfl | rfl
    · exact le_rfl
    · exact (PNat.lt_add_right a 1).le
    · exact (PNat.lt_add_right a 2).le
  have hxhi : x.1 ≤ a.1 + 2 := by
    rcases mem_ternaryBlock.mp hx with rfl | rfl | rfl
    · omega
    · have h1 : (a + 1).1 = a.1 + 1 := PNat.add_coe a 1
      omega
    · exact le_of_eq (PNat.add_coe a 2)
  have hylo : b.1 ≤ y.1 := by
    rcases mem_ternaryBlock.mp hy with rfl | rfl | rfl
    · exact le_rfl
    · exact (PNat.lt_add_right b 1).le
    · exact (PNat.lt_add_right b 2).le
  have hyhi : y.1 ≤ b.1 + 2 := by
    rcases mem_ternaryBlock.mp hy with rfl | rfl | rfl
    · omega
    · have h1 : (b + 1).1 = b.1 + 1 := PNat.add_coe b 1
      omega
    · exact le_of_eq (PNat.add_coe b 2)
  rcases le_total a.1 b.1 with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab] at h
    rw [Nat.dist_eq_sub_of_le (by omega)]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hba] at h
    rw [Nat.dist_eq_sub_of_le_right (by omega)]
    omega

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
