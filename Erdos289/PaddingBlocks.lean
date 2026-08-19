module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryConfigurations
public import Erdos289.NeutralAtoms

@[expose] public section

/-!
# Placing the padding states

The padding a current needs is a family of class-zero states of grade one,
pairwise compatible and compatible with everything already placed.  Below the
current every binary block has class zero (`Erdos289/NeutralAtoms.lean`), so
the only question is placement, and placement is elementary: put the blocks at
a fixed spacing, starting beyond the obstacle cutoff and ending below the
current.

The spacing is the constraint's own, `max 1 separation + 2`: two apart for the
blocks themselves and the separation margin between them.  Nothing here is a
choice that could have been made better; the spacing is forced and the count is
whatever fits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The spacing at which binary blocks of a constraint may be placed in a row. -/
def paddingSpacing (c : PhysicalConstraint) : ℕ := max 1 c.separation + 2

theorem paddingSpacing_pos (c : PhysicalConstraint) : 0 < paddingSpacing c := by
  unfold paddingSpacing; omega

/-- `h` binary blocks at the constraint's spacing, starting at `base`. -/
noncomputable def paddingBlocks (c : PhysicalConstraint) (base : ℕ) (hbase : 0 < base)
    (h : ℕ) : Finset Support :=
  (Finset.range h).image fun i =>
    binaryBlock ⟨base + i * paddingSpacing c, by omega⟩

theorem mem_paddingBlocks {c : PhysicalConstraint} {base : ℕ} (hbase : 0 < base)
    {h : ℕ} {S : Support} :
    S ∈ paddingBlocks c base hbase h ↔
      ∃ i < h, S = binaryBlock ⟨base + i * paddingSpacing c, by omega⟩ := by
  classical
  rw [paddingBlocks, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.1 hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, Finset.mem_range.2 hi, rfl⟩

theorem card_paddingBlocks (c : PhysicalConstraint) {base : ℕ} (hbase : 0 < base)
    (h : ℕ) : (paddingBlocks c base hbase h).card = h := by
  classical
  rw [paddingBlocks, Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ hij
  have hstart := congrArg Subtype.val (binaryBlock_injective hij)
  have hd := paddingSpacing_pos c
  simp only [] at hstart
  exact Nat.eq_of_mul_eq_mul_right hd (by omega)

/--
The padding family: `h` binary blocks of class zero, pairwise compatible, all
beyond the obstacle cutoff and all below the current.
-/
theorem paddingBlocks_spec
    (c : PhysicalConstraint) {Q base h : ℕ} (hbase : 0 < base)
    (hcut : c.obstacleCutoff < base)
    (hfit : base + h * paddingSpacing c + 1 < Q) :
    (∀ S ∈ paddingBlocks c base hbase h, S.Admissible smallBlockSizes c) ∧
      (∀ S ∈ paddingBlocks c base hbase h, S.FactorsThroughPrimePowerStage Q) ∧
      (∀ S ∈ paddingBlocks c base hbase h,
        ∀ hfac : S.FactorsThroughPrimePowerStage Q, S.simpleFibreClass hfac = 0) ∧
      ((paddingBlocks c base hbase h : Set Support).Pairwise
        fun S T ↦ S.CompatibleFor T c) ∧
      (∀ S ∈ paddingBlocks c base hbase h, S.grade = 1) ∧
      (∀ S ∈ paddingBlocks c base hbase h, S.value < 2 / (base : ℚ)) := by
  classical
  have hd := paddingSpacing_pos c
  have hstart : ∀ i, i < h →
      ((⟨base + i * paddingSpacing c, by omega⟩ : Denominator)).1 + 1 < Q := by
    intro i hi
    have : i * paddingSpacing c ≤ h * paddingSpacing c :=
      Nat.mul_le_mul_right _ (le_of_lt hi)
    simp only []
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hS
    exact binaryBlock_admissible c _ (by simp only []; omega)
  · intro S hS
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hS
    exact binaryBlock_factorsThroughPrimePowerStage (hstart i hi)
  · intro S hS hfac
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hS
    exact binaryBlock_simpleFibreClass_eq_zero (hstart i hi) hfac
  · intro S hS T hT hST
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hS
    obtain ⟨j, hj, rfl⟩ := (mem_paddingBlocks hbase).1 hT
    have hij : i ≠ j := by
      intro hEq
      exact hST (by rw [hEq])
    have hsep : max 1 c.separation + 2 ≤ paddingSpacing c := by
      unfold paddingSpacing; omega
    have hdist : max 1 c.separation + 1 <
        Nat.dist ((⟨base + i * paddingSpacing c, by omega⟩ : Denominator)).1
          ((⟨base + j * paddingSpacing c, by omega⟩ : Denominator)).1 := by
      show max 1 c.separation + 1 <
        Nat.dist (base + i * paddingSpacing c) (base + j * paddingSpacing c)
      rw [Nat.dist]
      rcases Nat.lt_or_ge i j with hlt | hge
      · have hstep : i * paddingSpacing c + paddingSpacing c
            ≤ j * paddingSpacing c := by
          calc i * paddingSpacing c + paddingSpacing c
              = (i + 1) * paddingSpacing c := by ring
            _ ≤ j * paddingSpacing c := Nat.mul_le_mul_right _ hlt
        omega
      · have hji : j < i := by omega
        have hstep : j * paddingSpacing c + paddingSpacing c
            ≤ i * paddingSpacing c := by
          calc j * paddingSpacing c + paddingSpacing c
              = (j + 1) * paddingSpacing c := by ring
            _ ≤ i * paddingSpacing c := Nat.mul_le_mul_right _ hji
        omega
    have hcross := binaryBlock_crossSeparated_of_dist (m := c.separation)
      (lt_of_le_of_lt (by omega) hdist)
    have hcross1 := binaryBlock_crossSeparated_of_dist (m := 1)
      (lt_of_le_of_lt (by omega) hdist)
    exact ⟨crossSeparated_graphDisjoint hcross1, hcross⟩
  · intro S hS
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hS
    exact binaryBlock_grade _
  · intro S hS
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hS
    have hb : (0 : ℚ) < (base : ℚ) := by exact_mod_cast hbase
    have hle : (base : ℚ)
        ≤ ((⟨base + i * paddingSpacing c, by omega⟩ : Denominator)).1 := by
      show (base : ℚ) ≤ ((base + i * paddingSpacing c : ℕ) : ℚ)
      exact_mod_cast Nat.le_add_right base (i * paddingSpacing c)
    calc (binaryBlock (⟨base + i * paddingSpacing c, by omega⟩ : Denominator)).value
        = binaryBlockMass ⟨base + i * paddingSpacing c, by omega⟩ :=
          binaryBlock_value _
      _ < 2 / (((⟨base + i * paddingSpacing c, by omega⟩ : Denominator)).1 : ℚ) :=
          binaryBlockMass_lt_two_div _
      _ ≤ 2 / (base : ℚ) := div_le_div_of_nonneg_left (by norm_num) hb hle

end Erdos289
