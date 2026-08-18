module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimePowerFiltration
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Distinct coefficients are distinct classes at a prime current

At a prime current `Q = p` the signed-inverse atoms of a row have distinguished
denominators `p k` with pairwise distinct coefficients `k`, and every `k` of a
row satisfies `0 < k < p`.  Their images in the simple fibre are then pairwise
distinct, because

`1/(p k) - 1/(p k') = (k' - k) / (p k k')`

has a denominator whose `p`-part survives: the lower stage is annihilated by an
integer `L` with `p ∤ L`, while `p ∤ k' - k`.

The consequence is that a prime row has simple-fibre multiplicity one, so its
image in the fibre is as large as the row itself.  That is what feeds the
Dias da Silva–Hamidoune interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/--
Two distinguished reciprocals of a prime current with distinct coefficients
below the prime differ by an element outside the lower stage.
-/
theorem reciprocalResidue_sub_notMem_lower
    {p k k' : ℕ} (hp : p.Prime) (hk : 0 < k) (hk' : 0 < k')
    (hkp : k < p) (hk'p : k' < p) (hne : k ≠ k')
    (hkpos : 0 < p * k) (hk'pos : 0 < p * k') :
    reciprocalResidue ⟨p * k, hkpos⟩ - reciprocalResidue ⟨p * k', hk'pos⟩
      ∉ lowerPrimePowerStage p := by
  intro hmem
  obtain ⟨L, hLpos, hLann, hLndvd⟩ :=
    exists_lowerAnnihilator (Q := p) hp Nat.one_pos (pow_one p).symm
  rw [pow_one] at hLndvd
  have hppos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hk'Q : (0 : ℚ) < (k' : ℚ) := by exact_mod_cast hk'
  -- the difference, as a centered rational
  have hval : reciprocalResidue ⟨p * k, hkpos⟩ - reciprocalResidue ⟨p * k', hk'pos⟩
      = AffineCorrection.CenteredValue.mk (1 : ℚ)
        (1 / ((p : ℚ) * k) - 1 / ((p : ℚ) * k')) := by
    show AffineCorrection.CenteredValue.mk (1 : ℚ) (reciprocal ⟨p * k, hkpos⟩)
        - AffineCorrection.CenteredValue.mk (1 : ℚ) (reciprocal ⟨p * k', hk'pos⟩) = _
    rw [← map_sub]
    congr 1
    show (1 : ℚ) / ((p * k : ℕ) : ℚ) - 1 / ((p * k' : ℕ) : ℚ) = _
    push_cast
    ring
  rw [hval] at hmem
  have hzero := hLann _ hmem
  rw [← map_nsmul] at hzero
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 hzero)
  rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hz
  -- clear denominators
  have hQeq : (z : ℚ) * ((p : ℚ) * k * k') = (L : ℚ) * ((k' : ℚ) - k) := by
    rw [hz]
    field_simp
  have hZeq : z * ((p : ℤ) * k * k') = (L : ℤ) * ((k' : ℤ) - k) := by exact_mod_cast hQeq
  have hdvdZ : (p : ℤ) ∣ (L : ℤ) * ((k' : ℤ) - k) := ⟨z * k * k', by rw [← hZeq]; ring⟩
  have hdvdN : p ∣ L * ((k' : ℤ) - (k : ℤ)).natAbs := by
    have h1 := Int.natAbs_dvd_natAbs.2 hdvdZ
    simpa [Int.natAbs_mul] using h1
  have hkZ : (k : ℤ) < p := by exact_mod_cast hkp
  have hk'Z : (k' : ℤ) < p := by exact_mod_cast hk'p
  have hkZ0 : (0 : ℤ) < k := by exact_mod_cast hk
  have hk'Z0 : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hnlt : ((k' : ℤ) - k).natAbs < p := by omega
  have hn0 : ((k' : ℤ) - k).natAbs ≠ 0 := by
    intro h0
    have hz0 : (k' : ℤ) - k = 0 := Int.natAbs_eq_zero.1 h0
    exact hne (by omega)
  rcases (Nat.Prime.dvd_mul hp).1 hdvdN with hL | hd
  · exact hLndvd hL
  · have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd
    omega

end Erdos289
