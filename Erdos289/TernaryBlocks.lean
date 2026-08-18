module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryBlocks

@[expose] public section

/-!
# Canonical ternary path blocks and the endpoint inclusion switch

The physical endpoint switch is the inclusion of the adjacent binary interval
`{a+1,a+2}` into the adjacent ternary interval `{a,a+1,a+2}`.  Both supports
have one connected component and their exact-value difference is `1/a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The connected three-denominator support beginning at `a`. -/
def ternaryBlock (a : Denominator) : Support := {a, a + 1, a + 2}

@[simp]
theorem mem_ternaryBlock {a n : Denominator} :
    n ∈ ternaryBlock a ↔ n = a ∨ n = a + 1 ∨ n = a + 2 := by
  simp [ternaryBlock]

theorem ternaryBlock_card (a : Denominator) : (ternaryBlock a).card = 3 := by
  have h01 : a ≠ a + 1 := ne_of_lt (PNat.lt_add_right a 1)
  have h02 : a ≠ a + 2 := ne_of_lt (PNat.lt_add_right a 2)
  have h12 : a + 1 ≠ a + 2 := by
    intro h
    have hv := congrArg Subtype.val h
    have h1 : (a + 1).1 = a.1 + 1 := PNat.add_coe a 1
    have h2 : (a + 2).1 = a.1 + 2 := PNat.add_coe a 2
    omega
  simp [ternaryBlock, h01, h02, h12]

theorem ternaryBlock_preconnected (a : Denominator) :
    (ternaryBlock a).graph.Preconnected := by
  let base : {n : Denominator // n ∈ ternaryBlock a} := ⟨a, by simp⟩
  have toBase : ∀ x : {n : Denominator // n ∈ ternaryBlock a},
      (ternaryBlock a).graph.Reachable x base := by
    intro x
    rcases mem_ternaryBlock.mp x.property with hx | hx | hx
    · have hxb : x = base := by
        apply Subtype.ext
        exact hx
      exact hxb ▸ .rfl
    · apply SimpleGraph.Adj.reachable
      change denominatorPath.Adj x.1 base.1
      rw [hx]
      exact Or.inr (PNat.add_coe a 1).symm
    · have h21 : (ternaryBlock a).graph.Adj x
          ⟨a + 1, by simp⟩ := by
        change denominatorPath.Adj x.1 (a + 1)
        rw [hx]
        right
        have h1 : (a + 1).1 = a.1 + 1 := PNat.add_coe a 1
        have h2 : (a + 2).1 = a.1 + 2 := PNat.add_coe a 2
        omega
      have h10 : (ternaryBlock a).graph.Adj
          ⟨a + 1, by simp⟩ base := by
        change denominatorPath.Adj (a + 1) a
        exact Or.inr (PNat.add_coe a 1).symm
      exact (SimpleGraph.Adj.reachable h21).trans
        (SimpleGraph.Adj.reachable h10)
  intro x y
  exact (toBase x).trans (toBase y).symm

theorem ternaryBlock_grade (a : Denominator) : (ternaryBlock a).grade = 1 := by
  let _ : Nonempty {n : Denominator // n ∈ ternaryBlock a} :=
    ⟨⟨a, by simp⟩⟩
  let _ : Subsingleton (ternaryBlock a).Blocks :=
    (ternaryBlock_preconnected a).subsingleton_connectedComponent
  exact Nat.card_unique

theorem ternaryBlock_blockSize (a : Denominator)
    (c : (ternaryBlock a).Blocks) :
    (ternaryBlock a).blockSize c = 3 := by
  have hsupp : c.supp = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound
      (ternaryBlock_preconnected a c.exists_rep.choose x)).symm.trans
        c.exists_rep.choose_spec
  rw [Support.blockSize, hsupp]
  calc
    Nat.card ↑(Set.univ : Set {n : Denominator // n ∈ ternaryBlock a}) =
        Nat.card {n : Denominator // n ∈ ternaryBlock a} :=
      Nat.card_congr (Equiv.Set.univ _)
    _ = Fintype.card {n : Denominator // n ∈ ternaryBlock a} :=
      Nat.card_eq_fintype_card
    _ = (ternaryBlock a).card := Fintype.card_coe _
    _ = 3 := ternaryBlock_card a

theorem ternaryBlock_hasBlockSizes (a : Denominator) :
    (ternaryBlock a).HasBlockSizes smallBlockSizes := by
  intro c
  change (ternaryBlock a).blockSize c = 2 ∨
    (ternaryBlock a).blockSize c = 3
  exact Or.inr (ternaryBlock_blockSize a c)

theorem ternaryBlock_avoids
    (c : PhysicalConstraint) (a : Denominator)
    (ha : c.obstacleCutoff < a.1) :
    (ternaryBlock a).Avoids c := by
  rw [Support.Avoids, Finset.disjoint_left]
  intro n hnblock hnobs
  have hnle := c.le_obstacleCutoff hnobs
  rcases mem_ternaryBlock.mp hnblock with rfl | hna | hna
  · omega
  · have haval : a.1 < n.1 := by
      rw [hna]
      exact PNat.lt_add_right a 1
    omega
  · have haval : a.1 < n.1 := by
      rw [hna]
      exact PNat.lt_add_right a 2
    omega

theorem ternaryBlock_separated (a : Denominator) (margin : ℕ) :
    (ternaryBlock a).Separated margin := by
  intro c d hcd
  let _ : Subsingleton (ternaryBlock a).Blocks :=
    (ternaryBlock_preconnected a).subsingleton_connectedComponent
  exact (hcd (Subsingleton.elim c d)).elim

theorem ternaryBlock_admissible
    (c : PhysicalConstraint) (a : Denominator)
    (ha : c.obstacleCutoff < a.1) :
    (ternaryBlock a).Admissible smallBlockSizes c :=
  ⟨ternaryBlock_hasBlockSizes a, ternaryBlock_avoids c a ha,
    ternaryBlock_separated a c.separation⟩

@[simp]
theorem ternaryBlock_value (a : Denominator) :
    (ternaryBlock a).value = reciprocal a + binaryBlockMass (a + 1) := by
  have h01 : a ≠ a + 1 := ne_of_lt (PNat.lt_add_right a 1)
  have h02 : a ≠ a + 2 := ne_of_lt (PNat.lt_add_right a 2)
  have h12 : a + 1 ≠ a + 2 := by
    intro h
    have hv := congrArg Subtype.val h
    have h1 : (a + 1).1 = a.1 + 1 := PNat.add_coe a 1
    have h2 : (a + 2).1 = a.1 + 2 := PNat.add_coe a 2
    omega
  simp [ternaryBlock, Support.value, reciprocal, binaryBlockMass, h01, h02,
    h12]
  norm_cast

/-- The endpoint inclusion switch preserves grade and adds exactly `1/a`. -/
theorem endpoint_inclusion_switch (a : Denominator) :
    (ternaryBlock a).value =
      (binaryBlock (a + 1)).value + reciprocal a := by
  rw [ternaryBlock_value, binaryBlock_value]
  ac_rfl

end Erdos289
