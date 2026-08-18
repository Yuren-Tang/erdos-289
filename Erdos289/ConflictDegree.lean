module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryConfigurations
public import Erdos289.TransverseReservoir

@[expose] public section

/-!
# The conflict graph of a binary-atom reservoir has bounded degree

Every atom produced by the signed-inverse construction is a binary block, and
distinct atoms of one row have distinct starts.  Two binary blocks conflict
only when their starts lie in a window whose width depends on the separation
margin of the physical constraint and on nothing else — in particular not on
the current prime power, on the row size, or on how large the denominators are.

This is the input the packing theorem needs: the maximum degree `Δ` has to be a
constant before `2Δ`-thickness can be compared against a row size that grows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- Binary atoms whose starts are far apart are physically compatible. -/
theorem binaryBlock_compatibleFor_of_dist
    {a b : Denominator} {c : PhysicalConstraint}
    (h : max 1 c.separation + 1 < Nat.dist a.1 b.1) :
    (binaryBlock a).CompatibleFor (binaryBlock b) c := by
  have hcs : (binaryBlock a).CrossSeparated (binaryBlock b) (max 1 c.separation) := by
    rcases Nat.lt_or_ge a.1 b.1 with hab | hab
    · refine binaryBlock_crossSeparated_of_lt ?_
      rw [Nat.dist_eq_sub_of_le hab.le] at h
      omega
    · refine binaryBlock_crossSeparated_of_gt ?_
      rw [Nat.dist_eq_sub_of_le_right hab] at h
      omega
  exact ⟨crossSeparated_graphDisjoint
      (crossSeparated_mono hcs (Nat.le_max_left 1 c.separation)),
    crossSeparated_mono hcs (Nat.le_max_right 1 c.separation)⟩

/-- Conflicting binary atoms have nearby starts. -/
theorem dist_le_of_not_binaryBlock_compatibleFor
    {a b : Denominator} {c : PhysicalConstraint}
    (h : ¬ (binaryBlock a).CompatibleFor (binaryBlock b) c) :
    Nat.dist a.1 b.1 ≤ max 1 c.separation + 1 := by
  by_contra hcon
  exact h (binaryBlock_compatibleFor_of_dist (by omega))

/-- A punctured window of radius `w` around a natural number holds `2w` points. -/
theorem card_punctured_window_le (T : Finset ℕ) (x w : ℕ) :
    (T.filter fun y => y ≠ x ∧ Nat.dist x y ≤ w).card ≤ 2 * w := by
  classical
  have hsub : T.filter (fun y => y ≠ x ∧ Nat.dist x y ≤ w) ⊆
      (Finset.Icc (x - w) (x + w)).erase x := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨-, hne, hdist⟩
    refine Finset.mem_erase.mpr ⟨hne, Finset.mem_Icc.mpr ?_⟩
    rw [Nat.dist] at hdist
    omega
  have hmem : x ∈ Finset.Icc (x - w) (x + w) := Finset.mem_Icc.mpr (by omega)
  calc
    (T.filter fun y => y ≠ x ∧ Nat.dist x y ≤ w).card
        ≤ ((Finset.Icc (x - w) (x + w)).erase x).card := Finset.card_le_card hsub
    _ = (Finset.Icc (x - w) (x + w)).card - 1 := Finset.card_erase_of_mem hmem
    _ ≤ 2 * w := by
      rw [Nat.card_Icc]
      omega

/-- The same bound for a set of denominators. -/
theorem card_nearby_starts_le
    (starts : Finset Denominator) (a : Denominator) (w : ℕ) :
    (starts.filter fun b => b ≠ a ∧ Nat.dist a.1 b.1 ≤ w).card ≤ 2 * w := by
  classical
  refine le_trans (Finset.card_le_card_of_injOn PNat.val ?_ ?_)
    (card_punctured_window_le (starts.image PNat.val) a.1 w)
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbs, hne, hdist⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ hbs, fun hval => hne (PNat.coe_injective hval), hdist⟩
  · intro x _ y _ hxy
    exact PNat.coe_injective hxy

/--
The conflict degree of a family of binary atoms is bounded by a constant
depending only on the separation margin.  The statement takes the conflict
neighbourhood as data so that it applies to any presentation of it, whatever
decidability instance that presentation was built with.
-/
theorem binaryConflict_card_le
    (c : PhysicalConstraint) (starts : Finset Denominator) (a : Denominator)
    (N : Finset Support)
    (hN : ∀ T ∈ N, (∃ b ∈ starts, T = binaryBlock b) ∧ T ≠ binaryBlock a ∧
      ¬ (binaryBlock a).CompatibleFor T c) :
    N.card ≤ 2 * (max 1 c.separation + 1) := by
  classical
  set w := max 1 c.separation + 1 with hw
  have hsub : N ⊆ (starts.filter fun b => b ≠ a ∧ Nat.dist a.1 b.1 ≤ w).image binaryBlock := by
    intro T hT
    rcases hN T hT with ⟨⟨b, hb, rfl⟩, hTne, hTconf⟩
    refine Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, ?_, ?_⟩, rfl⟩
    · intro hba
      exact hTne (by rw [hba])
    · exact dist_le_of_not_binaryBlock_compatibleFor hTconf
  calc
    N.card ≤ ((starts.filter fun b => b ≠ a ∧ Nat.dist a.1 b.1 ≤ w).image binaryBlock).card :=
      Finset.card_le_card hsub
    _ ≤ (starts.filter fun b => b ≠ a ∧ Nat.dist a.1 b.1 ≤ w).card := Finset.card_image_le
    _ ≤ 2 * w := card_nearby_starts_le starts a w

/--
Reservoir form: a transverse reservoir whose atoms are binary blocks has
conflict degree at most `2 (max 1 separation + 1)`, a constant.
-/
theorem TransverseReservoir.conflictNeighbors_card_le_of_binary
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    (starts : Finset Denominator) (hatoms : R.atoms = starts.image binaryBlock)
    (a : Denominator) :
    (R.conflictNeighbors (binaryBlock a)).card ≤ 2 * (max 1 c.separation + 1) := by
  classical
  refine binaryConflict_card_le c starts a _ ?_
  intro T hT
  have hmem : T ∈ R.atoms ∧ T ≠ binaryBlock a ∧
      ¬ (binaryBlock a).CompatibleFor T c := by
    simpa [TransverseReservoir.conflictNeighbors] using hT
  refine ⟨?_, hmem.2.1, hmem.2.2⟩
  rw [hatoms] at hmem
  rcases Finset.mem_image.mp hmem.1 with ⟨b, hb, hTb⟩
  exact ⟨b, hb, hTb.symm⟩

end Erdos289
