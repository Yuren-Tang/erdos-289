module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.ReciprocalIdentities
public import Erdos289.PhysicalSupports
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Canonical binary path blocks

The public object is the two-vertex connected support.  Polynomial indices
used to construct particular blocks remain in the arithmetic provider layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

theorem binaryBlockMass_pos (a : Denominator) : 0 < binaryBlockMass a := by
  unfold binaryBlockMass
  have ha : (0 : ℚ) < a.1 := by exact_mod_cast a.2
  positivity

theorem binaryBlockMass_lt_two_div (a : Denominator) :
    binaryBlockMass a < 2 / (a.1 : ℚ) := by
  have ha : (0 : ℚ) < a.1 := by exact_mod_cast a.2
  have ha1 : (0 : ℚ) < a.1 + 1 := by positivity
  have ha0 : (a.1 : ℚ) ≠ 0 := ne_of_gt ha
  have ha10 : (a.1 : ℚ) + 1 ≠ 0 := ne_of_gt ha1
  unfold binaryBlockMass
  field_simp [ha0, ha10]
  nlinarith

/-- The connected two-denominator support beginning at `a`. -/
def binaryBlock (a : Denominator) : Support := {a, a + 1}

@[simp]
theorem mem_binaryBlock {a n : Denominator} :
    n ∈ binaryBlock a ↔ n = a ∨ n = a + 1 := by
  simp [binaryBlock]

theorem binaryBlock_card (a : Denominator) : (binaryBlock a).card = 2 := by
  have hne : a ≠ a + 1 := ne_of_lt (PNat.lt_add_right a 1)
  simp [binaryBlock, hne]

theorem binaryBlock_preconnected (a : Denominator) :
    (binaryBlock a).graph.Preconnected := by
  intro x y
  rcases (mem_binaryBlock.mp x.property) with hx | hx <;>
    rcases (mem_binaryBlock.mp y.property) with hy | hy
  · exact (Subtype.ext (hx.trans hy.symm)) ▸ .rfl
  · exact SimpleGraph.Adj.reachable (by
      change denominatorPath.Adj x.1 y.1
      rw [hx, hy]
      exact Or.inl (PNat.add_coe a 1).symm)
  · exact SimpleGraph.Adj.reachable (by
      change denominatorPath.Adj x.1 y.1
      rw [hx, hy]
      exact Or.inr (PNat.add_coe a 1).symm)
  · exact (Subtype.ext (hx.trans hy.symm)) ▸ .rfl

theorem binaryBlock_grade (a : Denominator) : (binaryBlock a).grade = 1 := by
  let _ : Nonempty {n : Denominator // n ∈ binaryBlock a} :=
    ⟨⟨a, by simp⟩⟩
  let _ : Subsingleton (binaryBlock a).Blocks :=
    (binaryBlock_preconnected a).subsingleton_connectedComponent
  exact Nat.card_unique

theorem binaryBlock_blockSize (a : Denominator)
    (c : (binaryBlock a).Blocks) :
    (binaryBlock a).blockSize c = 2 := by
  have hsupp : c.supp = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound
      (binaryBlock_preconnected a c.exists_rep.choose x)).symm.trans
        c.exists_rep.choose_spec
  rw [Support.blockSize, hsupp]
  calc
    Nat.card ↑(Set.univ : Set {n : Denominator // n ∈ binaryBlock a}) =
        Nat.card {n : Denominator // n ∈ binaryBlock a} :=
      Nat.card_congr (Equiv.Set.univ _)
    _ = Fintype.card {n : Denominator // n ∈ binaryBlock a} :=
      Nat.card_eq_fintype_card
    _ = (binaryBlock a).card := Fintype.card_coe _
    _ = 2 := binaryBlock_card a

theorem binaryBlock_hasBlockSizes (a : Denominator) :
    (binaryBlock a).HasBlockSizes smallBlockSizes := by
  intro c
  change (binaryBlock a).blockSize c = 2 ∨ (binaryBlock a).blockSize c = 3
  exact Or.inl (binaryBlock_blockSize a c)

/-- Largest forbidden denominator, with value zero for the empty obstacle. -/
def PhysicalConstraint.obstacleCutoff (c : PhysicalConstraint) : ℕ :=
  c.obstacle.sup fun n => n.1

theorem PhysicalConstraint.le_obstacleCutoff
    {c : PhysicalConstraint} {n : Denominator} (hn : n ∈ c.obstacle) :
    n.1 ≤ c.obstacleCutoff := by
  exact Finset.le_sup hn

/-- A binary block beginning beyond the obstacle cutoff avoids the obstacle. -/
theorem binaryBlock_avoids
    (c : PhysicalConstraint) (a : Denominator)
    (ha : c.obstacleCutoff < a.1) :
    (binaryBlock a).Avoids c := by
  rw [Support.Avoids, Finset.disjoint_left]
  intro n hnblock hnobs
  have hnle := c.le_obstacleCutoff hnobs
  rcases mem_binaryBlock.mp hnblock with rfl | hna
  · omega
  · have haval : a.1 < n.1 := by
      rw [hna]
      exact PNat.lt_add_right a 1
    omega

/-- A single connected block satisfies every inter-block separation margin. -/
theorem binaryBlock_separated (a : Denominator) (margin : ℕ) :
    (binaryBlock a).Separated margin := by
  intro c d hcd
  let _ : Subsingleton (binaryBlock a).Blocks :=
    (binaryBlock_preconnected a).subsingleton_connectedComponent
  exact (hcd (Subsingleton.elim c d)).elim

/-- Every sufficiently remote binary block is an admissible `{2,3}` support. -/
theorem binaryBlock_admissible
    (c : PhysicalConstraint) (a : Denominator)
    (ha : c.obstacleCutoff < a.1) :
    (binaryBlock a).Admissible smallBlockSizes c :=
  ⟨binaryBlock_hasBlockSizes a, binaryBlock_avoids c a ha,
    binaryBlock_separated a c.separation⟩

@[simp]
theorem binaryBlock_value (a : Denominator) :
    (binaryBlock a).value = binaryBlockMass a := by
  have hne : a ≠ a + 1 := ne_of_lt (PNat.lt_add_right a 1)
  simp only [binaryBlock, Support.value, binaryBlockMass, reciprocal,
    Finset.sum_insert, Finset.mem_singleton, hne, not_false_eq_true,
    Finset.sum_singleton]
  congr 2
  norm_cast

end Erdos289
