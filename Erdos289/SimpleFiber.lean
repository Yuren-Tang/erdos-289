module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimePowerFiltration
public import Mathlib.Algebra.CharZero.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

/-!
# Canonical algebra of a prime-power simple fibre

The public conclusion is that the intrinsic subquotient at `Q = p^e` is a
one-dimensional additive `F_p`-object.  Rational representatives are used only
inside the proof that the current annihilator stage is cyclic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The canonical current-stage point represented by `1/Q`. -/
def primePowerGenerator (Q : ℕ) (hQ : 0 < Q) : PrimePowerSimpleFiber Q :=
  QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q)
    ⟨reciprocalResidue ⟨Q, hQ⟩,
      annihilatorStage_le Q (reciprocalResidue_mem_annihilatorStage ⟨Q, hQ⟩)⟩

private theorem annihilatorStage_eq_nsmul_reciprocal
    {Q : ℕ} (hQ : 0 < Q) {x : TargetResidue}
    (hx : x ∈ annihilatorStage Q) :
    ∃ k : Fin Q, x = k.1 • reciprocalResidue ⟨Q, hQ⟩ := by
  have hx0 : Q • x = Q • (0 : TargetResidue) := by
    change Q • x = 0 at hx
    simpa using hx
  rcases (QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff hQ.ne').mp hx0 with
    ⟨k, hk⟩
  refine ⟨k, ?_⟩
  simpa [reciprocalResidue, reciprocal, div_eq_mul_inv] using hk

/-- The canonical current point generates the entire intrinsic simple fibre. -/
theorem mem_zmultiples_primePowerGenerator
    {Q : ℕ} (hQ : 0 < Q) (x : PrimePowerSimpleFiber Q) :
    x ∈ AddSubgroup.zmultiples (primePowerGenerator Q hQ) := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
      rcases (AddSubgroup.mem_sup.mp x.2) with ⟨a, ha, b, hb, hab⟩
      rcases annihilatorStage_eq_nsmul_reciprocal hQ hb with ⟨k, hk⟩
      let a' : primePowerStage Q := ⟨a, lowerPrimePowerStage_le Q ha⟩
      let b' : primePowerStage Q := ⟨b, annihilatorStage_le Q hb⟩
      have hx : x = a' + b' := by
        apply Subtype.ext
        exact hab.symm
      have hb' : b' = k.1 •
          (⟨reciprocalResidue ⟨Q, hQ⟩,
            annihilatorStage_le Q
              (reciprocalResidue_mem_annihilatorStage ⟨Q, hQ⟩)⟩ :
            primePowerStage Q) := by
        apply Subtype.ext
        exact hk
      rw [AddSubgroup.mem_zmultiples_iff]
      refine ⟨(k.1 : ℤ), ?_⟩
      change (k.1 : ℤ) • primePowerGenerator Q hQ =
        QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) x
      rw [hx, map_add, hb', map_nsmul]
      have ha0 : QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) a' = 0 :=
        (QuotientAddGroup.eq_zero_iff a').2 ha
      rw [ha0, zero_add]
      simp [primePowerGenerator]

theorem primePowerGenerator_ne_zero
    {Q p e : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) :
    primePowerGenerator Q (hQ.symm ▸ pow_pos hp.pos e) ≠ 0 := by
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  intro hzero
  have hlower : reciprocalResidue ⟨Q, hQpos⟩ ∈ lowerPrimePowerStage Q := by
    exact (QuotientAddGroup.eq_zero_iff
      (⟨reciprocalResidue ⟨Q, hQpos⟩,
        annihilatorStage_le Q
          (reciprocalResidue_mem_annihilatorStage ⟨Q, hQpos⟩)⟩ :
        primePowerStage Q)).1 hzero
  apply reciprocalResidue_primePow_mul_not_mem_lower hp he hQ hQpos Nat.zero_lt_one
  simpa using hlower

theorem p_nsmul_primePowerGenerator_eq_zero
    {Q p e : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) :
    p • primePowerGenerator Q (hQ.symm ▸ pow_pos hp.pos e) = 0 := by
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  apply (QuotientAddGroup.eq_zero_iff
    (p • (⟨reciprocalResidue ⟨Q, hQpos⟩,
      annihilatorStage_le Q
        (reciprocalResidue_mem_annihilatorStage ⟨Q, hQpos⟩)⟩ :
      primePowerStage Q))).2
  change p • reciprocalResidue ⟨Q, hQpos⟩ ∈ lowerPrimePowerStage Q
  rcases e with _ | e
  · omega
  rcases e with _ | e
  · have hkill : p • reciprocalResidue ⟨Q, hQpos⟩ = 0 := by
      apply (nsmul_reciprocalResidue_eq_zero_iff p ⟨Q, hQpos⟩).2
      simp [hQ]
    exact hkill ▸ (lowerPrimePowerStage Q).zero_mem
  · let R := p ^ (e + 1)
    have hRpp : IsPrimePow R := ⟨p, e + 1, hp.prime, by omega, rfl⟩
    have hRQ : R < Q := by
      rw [hQ]
      exact Nat.pow_lt_pow_right hp.one_lt (by omega)
    have hmem : p • reciprocalResidue ⟨Q, hQpos⟩ ∈ annihilatorStage R := by
      change R • (p • reciprocalResidue ⟨Q, hQpos⟩) = 0
      rw [← mul_nsmul]
      have hmul : R * p = Q := by simp [R, hQ, pow_succ', mul_comm]
      rw [mul_comm p R, hmul]
      exact (nsmul_reciprocalResidue_eq_zero_iff Q ⟨Q, hQpos⟩).2 dvd_rfl
    have hle : annihilatorStage R ≤ lowerPrimePowerStage Q := by
      unfold lowerPrimePowerStage
      exact le_iSup_of_le R <| le_iSup_of_le hRQ <|
        le_iSup_of_le hRpp le_rfl
    exact hle hmem

/-- The intrinsic simple fibre at `p^e` is additively equivalent to `ZMod p`.
The equivalence is deliberately noncanonical: no basis enters the public
filtration or reservoir interfaces. -/
noncomputable def primePowerSimpleFiberAddEquiv
    {Q p e : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) :
    PrimePowerSimpleFiber Q ≃+ ZMod p := by
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  let g : PrimePowerSimpleFiber Q := primePowerGenerator Q hQpos
  have hgen : ∀ x : PrimePowerSimpleFiber Q, x ∈ AddSubgroup.zmultiples g :=
    mem_zmultiples_primePowerGenerator hQpos
  letI : Fact p.Prime := ⟨hp⟩
  have hgorder : addOrderOf g = p :=
    addOrderOf_eq_prime
      (p_nsmul_primePowerGenerator_eq_zero hp he hQ)
      (primePowerGenerator_ne_zero hp he hQ)
  have hcard : Nat.card (PrimePowerSimpleFiber Q) = p := by
    calc
      Nat.card (PrimePowerSimpleFiber Q) =
          Nat.card (AddSubgroup.zmultiples g) :=
        Nat.card_congr (Equiv.subtypeUnivEquiv hgen).symm
      _ = addOrderOf g := Nat.card_zmultiples g
      _ = p := hgorder
  exact (zmodAddEquivOfGenerator hgen hcard).symm

end Erdos289
