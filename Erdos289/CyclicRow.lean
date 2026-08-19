module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.LocalProfiles
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# Two classes suffice in a cyclic simple fibre

At a proper prime-power current the simple fibre is cyclic of prime order and
the atoms of a row need not have distinct classes, so the fixed-cardinality
fold of Dias da Silva–Hamidoune is not the mechanism.  The mechanism is the
cyclic one, and this module isolates its combinatorial content.

If a stock of atoms carries two *distinct* classes `c ≠ c'`, then for every
grade `h` at least the order of the fibre and every target class `v` there are
multiplicities `k₁ + k₂ = h` with `k₁` atoms of class `c` and `k₂` of class
`c'` summing to `v`.  Writing `d = c' - c ≠ 0`, the total class is
`h · c + k₂ · d`, and `d` is invertible, so `k₂` is determined modulo the
order; taking its least representative leaves `k₁ = h - k₂ ≥ 0` because
`h ≥ p > k₂`.

This is the grade-fibre epimorphism spectrum of one cyclic simple jump: it
contains every `h ≥ p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/--
Two distinct classes in a cyclic group of prime order realize every class at
every grade at least the order.
-/
theorem exists_multiplicities_of_two_classes
    {p : ℕ} [Fact p.Prime] (c c' : ZMod p) (hne : c ≠ c')
    {h : ℕ} (hh : p ≤ h) (v : ZMod p) :
    ∃ k₁ k₂ : ℕ, k₁ + k₂ = h ∧ k₂ < p ∧
      (k₁ : ZMod p) * c + (k₂ : ZMod p) * c' = v := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hd : c' - c ≠ 0 := sub_ne_zero_of_ne (Ne.symm hne)
  set w : ZMod p := (v - (h : ZMod p) * c) / (c' - c) with hw
  refine ⟨h - w.val, w.val, ?_, ?_, ?_⟩
  · have : w.val < p := ZMod.val_lt w
    omega
  · exact ZMod.val_lt w
  · have hvlt : w.val ≤ h := le_of_lt (lt_of_lt_of_le (ZMod.val_lt w) hh)
    have hcast : ((h - w.val : ℕ) : ZMod p) = (h : ZMod p) - (w.val : ZMod p) := by
      push_cast [Nat.cast_sub hvlt]
      ring
    have hwval : ((w.val : ℕ) : ZMod p) = w := by
      simp [ZMod.natCast_val, ZMod.cast_id]
    rw [hcast, hwval]
    have hmul : w * (c' - c) = v - (h : ZMod p) * c := by
      rw [hw, div_mul_cancel₀ _ hd]
    calc ((h : ZMod p) - w) * c + w * c'
        = (h : ZMod p) * c + w * (c' - c) := by ring
      _ = (h : ZMod p) * c + (v - (h : ZMod p) * c) := by rw [hmul]
      _ = v := by ring

/--
The same statement in the canonical simple fibre of a prime-power current: two
distinct classes of a row realize every class at every grade at least `p`.

This is the grade-fibre epimorphism spectrum of one cyclic simple jump, in the
form the tail chain needs.  Nothing about the current beyond `Q = p ^ e` enters,
so it serves the proper prime powers, where the fold of Dias da Silva–Hamidoune
does not apply.
-/
theorem exists_multiplicities_of_two_simpleFibreClasses
    {Q p e : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (c c' : PrimePowerSimpleFibre Q) (hne : c ≠ c')
    {h : ℕ} (hh : p ≤ h) (v : PrimePowerSimpleFibre Q) :
    ∃ k₁ k₂ : ℕ, k₁ + k₂ = h ∧ k₂ < p ∧ k₁ • c + k₂ • c' = v := by
  have : Fact p.Prime := ⟨hp⟩
  set φ := primePowerSimpleFibreAddEquiv hp he hQ with hφ
  have hneZ : φ c ≠ φ c' := fun hcon => hne (φ.injective hcon)
  obtain ⟨k₁, k₂, hsum, hlt, hclass⟩ :=
    exists_multiplicities_of_two_classes (φ c) (φ c') hneZ hh (φ v)
  refine ⟨k₁, k₂, hsum, hlt, φ.injective ?_⟩
  rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  exact hclass

end Erdos289
