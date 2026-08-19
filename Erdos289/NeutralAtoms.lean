module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryBlocks
public import Erdos289.TransverseReservoir

@[expose] public section

/-!
# States of class zero at a current

A binary block whose two denominators are both below the current is entirely
lower-supported: each of its two reciprocals is annihilated by a denominator
smaller than the current, so the block's residue lies in the lower stage and its
class in the simple fibre is zero.

These are the padding states.  They are abundant — every binary block below the
current is one — and they are exactly what a transverse pool cannot contain,
since transversality is nonvanishing in the fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

theorem binaryBlock_residue_mem_lowerPrimePowerStage
    {Q : ℕ} {a : Denominator} (h : a.1 + 1 < Q) :
    (binaryBlock a).residue ∈ lowerPrimePowerStage Q := by
  have hsucc : (a + 1).1 = a.1 + 1 := PNat.add_coe a 1
  have hne : a ≠ a + 1 := ne_of_lt (PNat.lt_add_right a 1)
  have hsum : (binaryBlock a).residue
      = reciprocalResidue a + reciprocalResidue (a + 1) := by
    rw [Support.residue_eq_sum, binaryBlock]
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [hsum]
  refine AddSubgroup.add_mem _ ?_ ?_
  · exact annihilatorStage_le_lower_of_lt a.2 (by omega)
      (reciprocalResidue_mem_annihilatorStage a)
  · exact annihilatorStage_le_lower_of_lt (a + 1).2 (by omega)
      (reciprocalResidue_mem_annihilatorStage (a + 1))

theorem binaryBlock_factorsThroughPrimePowerStage
    {Q : ℕ} {a : Denominator} (h : a.1 + 1 < Q) :
    (binaryBlock a).FactorsThroughPrimePowerStage Q :=
  lowerPrimePowerStage_le Q (binaryBlock_residue_mem_lowerPrimePowerStage h)

theorem binaryBlock_simpleFibreClass_eq_zero
    {Q : ℕ} {a : Denominator} (h : a.1 + 1 < Q)
    (hfac : (binaryBlock a).FactorsThroughPrimePowerStage Q) :
    (binaryBlock a).simpleFibreClass hfac = 0 :=
  (QuotientAddGroup.eq_zero_iff
    (⟨(binaryBlock a).residue, hfac⟩ : primePowerStage Q)).2
      (binaryBlock_residue_mem_lowerPrimePowerStage h)

end Erdos289
