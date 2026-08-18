module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryBlocks

@[expose] public section

/-!
# Finite configurations of remote binary blocks

A configuration is indexed only by its finite set of block starts.  The
placement predicate records the intrinsic physical facts needed downstream:
obstacle avoidance and pairwise separation.  It yields admissibility, exact
component grade, and exact reciprocal value without exposing any provider
formula used to choose the starts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- Union of the canonical binary blocks at the prescribed starts. -/
def binaryConfiguration (starts : Finset Denominator) : Support :=
  starts.biUnion binaryBlock

@[simp]
theorem binaryConfiguration_empty : binaryConfiguration ∅ = ∅ := by
  simp [binaryConfiguration]

theorem binaryConfiguration_insert {a : Denominator} {starts : Finset Denominator} :
    binaryConfiguration (insert a starts) =
      binaryBlock a ∪ binaryConfiguration starts := by
  simp [binaryConfiguration]

/-- Remote obstacle avoidance and pairwise physical separation of binary atoms. -/
def BinaryPlacement (c : PhysicalConstraint) (starts : Finset Denominator) : Prop :=
  (∀ a ∈ starts, c.obstacleCutoff < a.1) ∧
  ∀ a ∈ starts, ∀ b ∈ starts, a ≠ b →
    (binaryBlock a).CrossSeparated (binaryBlock b) (max 1 c.separation)

/-- An ordered gap of `m+1` between starts separates their binary blocks by `m`. -/
theorem binaryBlock_crossSeparated_of_lt {a b : Denominator} {m : ℕ}
    (h : a.1 + 1 + m < b.1) :
    (binaryBlock a).CrossSeparated (binaryBlock b) m := by
  intro x hx y hy
  have hxhi : x.1 ≤ a.1 + 1 := by
    rcases mem_binaryBlock.mp hx with rfl | rfl
    · omega
    · exact le_of_eq (PNat.add_coe a 1)
  have hylo : b.1 ≤ y.1 := by
    rcases mem_binaryBlock.mp hy with rfl | rfl
    · exact le_rfl
    · exact (PNat.lt_add_right b 1).le
  rw [Nat.dist_eq_sub_of_le (by omega)]
  omega

theorem binaryBlock_crossSeparated_of_gt {a b : Denominator} {m : ℕ}
    (h : b.1 + 1 + m < a.1) :
    (binaryBlock a).CrossSeparated (binaryBlock b) m := by
  intro x hx y hy
  rw [Nat.dist_comm]
  exact binaryBlock_crossSeparated_of_lt h y hy x hx

theorem crossSeparated_union_right {R S T : Support} {m : ℕ}
    (hRS : R.CrossSeparated S m) (hRT : R.CrossSeparated T m) :
    R.CrossSeparated (S ∪ T) m := by
  intro x hx y hy
  rcases Finset.mem_union.mp hy with hy | hy
  · exact hRS x hx y hy
  · exact hRT x hx y hy

theorem binaryBlock_graphDisjoint_configuration
    (c : PhysicalConstraint) {a : Denominator} {starts : Finset Denominator}
    (ha : a ∉ starts) (hplace : BinaryPlacement c (insert a starts)) :
    (binaryBlock a).GraphDisjoint (binaryConfiguration starts) := by
  apply crossSeparated_graphDisjoint
  intro x hx y hy
  rcases Finset.mem_biUnion.mp hy with ⟨b, hb, hyb⟩
  exact lt_of_le_of_lt (Nat.le_max_left 1 c.separation)
    (hplace.2 a (by simp) b (by simp [hb]) (by
      intro hab
      subst b
      exact ha hb) x hx y hyb)

theorem binaryConfiguration_admissible
    (c : PhysicalConstraint) (starts : Finset Denominator)
    (hplace : BinaryPlacement c starts) :
    (binaryConfiguration starts).Admissible smallBlockSizes c := by
  classical
  induction starts using Finset.induction with
  | empty =>
      simp [binaryConfiguration, Support.Admissible, Support.HasBlockSizes,
        Support.Avoids, Support.Separated]
  | @insert a starts ha ih =>
      rw [binaryConfiguration_insert]
      apply Support.admissible_union
      · exact binaryBlock_graphDisjoint_configuration c ha hplace
      · intro x hx y hy
        rcases Finset.mem_biUnion.mp hy with ⟨b, hb, hyb⟩
        exact lt_of_le_of_lt (Nat.le_max_right 1 c.separation)
          (hplace.2 a (by simp) b (by simp [hb]) (by
            intro hab
            subst b
            exact ha hb) x hx y hyb)
      · exact binaryBlock_admissible c a (hplace.1 a (by simp))
      · apply ih
        constructor
        · intro b hb
          exact hplace.1 b (by simp [hb])
        · intro b hb d hd hbd
          exact hplace.2 b (by simp [hb]) d (by simp [hd]) hbd

theorem binaryConfiguration_grade
    (c : PhysicalConstraint) (starts : Finset Denominator)
    (hplace : BinaryPlacement c starts) :
    (binaryConfiguration starts).grade = starts.card := by
  classical
  induction starts using Finset.induction with
  | empty => simp [binaryConfiguration, Support.grade]
  | @insert a starts ha ih =>
      rw [binaryConfiguration_insert]
      rw [Support.grade_union_of_graphDisjoint
        (binaryBlock_graphDisjoint_configuration c ha hplace)]
      rw [binaryBlock_grade, ih]
      · simp [ha, Nat.add_comm]
      · constructor
        · intro b hb
          exact hplace.1 b (by simp [hb])
        · intro b hb d hd hbd
          exact hplace.2 b (by simp [hb]) d (by simp [hd]) hbd

theorem binaryConfiguration_value
    (c : PhysicalConstraint) (starts : Finset Denominator)
    (hplace : BinaryPlacement c starts) :
    (binaryConfiguration starts).value = ∑ a ∈ starts, binaryBlockMass a := by
  classical
  induction starts using Finset.induction with
  | empty => simp [binaryConfiguration]
  | @insert a starts ha ih =>
      rw [binaryConfiguration_insert]
      rw [Support.value_union
        (binaryBlock_graphDisjoint_configuration c ha hplace).1]
      rw [binaryBlock_value, ih]
      · simp [ha]
      · constructor
        · intro b hb
          exact hplace.1 b (by simp [hb])
        · intro b hb d hd hbd
          exact hplace.2 b (by simp [hb]) d (by simp [hd]) hbd

end Erdos289
