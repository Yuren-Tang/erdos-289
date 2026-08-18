module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryBlocks
public import Erdos289.TransverseReservoir
public import Erdos289.SignedInverse

@[expose] public section

/-!
# Signed-inverse atoms at the arithmetic boundary

This internal module turns one good orientation of a complementary inverse
pair into the adjacent physical block used by the transverse-reservoir proof.
Only its stage-factorization theorem is intended to cross the arithmetic
boundary; the orientation coordinates remain implementation details.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

inductive Orientation
  | plus
  | minus
  deriving DecidableEq

/-- The complete finite set of signed-inverse orientations. -/
def orientations : Finset Orientation := {.plus, .minus}

def ComplementaryPair.coefficient {Q b : ℕ} (w : ComplementaryPair Q b) :
    Orientation → ℕ
  | .plus => w.kPlus
  | .minus => w.kMinus

def ComplementaryPair.inverseRepresentative {Q b : ℕ}
    (w : ComplementaryPair Q b) : Orientation → ℕ
  | .plus => w.cPlus
  | .minus => w.cMinus

def ComplementaryPair.start {Q b : ℕ} (w : ComplementaryPair Q b) :
    Orientation → ℕ
  | .plus => Q * w.kPlus
  | .minus => b * w.cMinus

theorem ComplementaryPair.start_pos {Q b : ℕ} (w : ComplementaryPair Q b)
    (hQ : 0 < Q) (s : Orientation) : 0 < w.start s := by
  cases s with
  | plus => exact Nat.mul_pos hQ w.kPlus_pos
  | minus => exact Nat.mul_pos (lt_trans w.kPlus_pos w.kPlus_lt) w.cMinus_pos

theorem ComplementaryPair.start_succ {Q b : ℕ} (w : ComplementaryPair Q b)
    (s : Orientation) :
    w.start s + 1 = match s with
      | .plus => b * w.cPlus
      | .minus => Q * w.kMinus := by
  cases s with
  | plus => simpa [ComplementaryPair.start] using w.plus_eq.symm
  | minus => simpa [ComplementaryPair.start] using w.minus_eq

/-- The distinguished `Q`-multiple is one of the two adjacent endpoints. -/
theorem ComplementaryPair.distinguished_le_start_succ
    {Q b : ℕ} (w : ComplementaryPair Q b) (s : Orientation) :
    Q * w.coefficient s ≤ w.start s + 1 := by
  cases s with
  | plus => simp [ComplementaryPair.start, ComplementaryPair.coefficient]
  | minus =>
      simpa [ComplementaryPair.start, ComplementaryPair.coefficient] using
        Nat.le_of_eq w.minus_eq.symm

/-- One orientation satisfying both current-unit and downward-companion conditions. -/
structure GoodOrientation (p : ℕ) {Q b : ℕ} (w : ComplementaryPair Q b) where
  sign : Orientation
  coefficient_unit : ¬p ∣ w.coefficient sign
  companion_coprime : b.Coprime (w.inverseRepresentative sign)

/-- All usable orientations of one complementary inverse pair.  Keeping this
finite feasibility set, rather than selecting one sign, is essential: sign is
only witness-level data and global thinning may use either orientation. -/
def ComplementaryPair.goodOrientations {Q b : ℕ}
    (w : ComplementaryPair Q b) (p : ℕ) : Finset Orientation :=
  orientations.filter fun s ↦
    ¬p ∣ w.coefficient s ∧ b.Coprime (w.inverseRepresentative s)

@[simp]
theorem ComplementaryPair.mem_goodOrientations_iff
    {Q b p : ℕ} (w : ComplementaryPair Q b) (s : Orientation) :
    s ∈ w.goodOrientations p ↔
      ¬p ∣ w.coefficient s ∧ b.Coprime (w.inverseRepresentative s) := by
  cases s <;> simp [ComplementaryPair.goodOrientations, orientations]

/-- Membership in the feasibility set is precisely the certificate needed to
realize an oriented atom. -/
def ComplementaryPair.goodOrientationOfMem
    {Q b p : ℕ} (w : ComplementaryPair Q b) (s : Orientation)
    (hs : s ∈ w.goodOrientations p) : GoodOrientation p w where
  sign := s
  coefficient_unit := (w.mem_goodOrientations_iff s).1 hs |>.1
  companion_coprime := (w.mem_goodOrientations_iff s).1 hs |>.2

/-- For a prime carrier, failure of downward coprimality is exactly divisibility
of the inverse representative by that carrier. -/
theorem ComplementaryPair.not_companionCoprime_iff_dvd
    {Q b : ℕ} (w : ComplementaryPair Q b) (hb : b.Prime)
    (s : Orientation) :
    ¬b.Coprime (w.inverseRepresentative s) ↔
      b ∣ w.inverseRepresentative s := by
  rw [hb.dvd_iff_not_coprime]

/-- A downwardness exception has the intrinsic quadratic shape forced by the
inverse equation.  The two displayed equations are kept in one theorem; the
orientation split is proof technology, not a provider-level case distinction. -/
theorem ComplementaryPair.exception_quadratic_shape
    {Q b : ℕ} (w : ComplementaryPair Q b) (hb : b.Prime)
    (s : Orientation) (hs : ¬b.Coprime (w.inverseRepresentative s)) :
    ∃ ell : ℕ,
      w.inverseRepresentative s = ell * b ∧
      match s with
      | .plus => ell * b ^ 2 = Q * w.kPlus + 1
      | .minus => ell * b ^ 2 + 1 = Q * w.kMinus := by
  have hdvd : b ∣ w.inverseRepresentative s :=
    (w.not_companionCoprime_iff_dvd hb s).1 hs
  rcases hdvd with ⟨ell, hell⟩
  refine ⟨ell, by simpa [mul_comm] using hell, ?_⟩
  cases s with
  | plus =>
      change w.cPlus = b * ell at hell
      calc
        ell * b ^ 2 = b * (b * ell) := by ring
        _ = b * w.cPlus := by rw [hell]
        _ = Q * w.kPlus + 1 := w.plus_eq
  | minus =>
      change w.cMinus = b * ell at hell
      calc
        ell * b ^ 2 + 1 = b * (b * ell) + 1 := by ring
        _ = b * w.cMinus + 1 := by rw [hell]
        _ = Q * w.kMinus := w.minus_eq

/-- The adjacent length-two atom represented by a good orientation. -/
def GoodOrientation.atom {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hQ : 0 < Q) : Support :=
  binaryBlock ⟨w.start g.sign, w.start_pos hQ g.sign⟩

/-- Exact physical mass of an oriented atom is controlled solely by its
intrinsic left endpoint. -/
theorem GoodOrientation.atom_value_lt_two_div_start
    {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hQ : 0 < Q) :
    (g.atom hQ).value < 2 / (w.start g.sign : ℚ) := by
  let a : Denominator := ⟨w.start g.sign, w.start_pos hQ g.sign⟩
  change (binaryBlock a).value < 2 / (a.1 : ℚ)
  rw [binaryBlock_value]
  exact binaryBlockMass_lt_two_div _

theorem coefficient_pos_lt
    {Q b : ℕ} (w : ComplementaryPair Q b) (s : Orientation) :
    0 < w.coefficient s ∧ w.coefficient s < b := by
  cases s <;> simp [ComplementaryPair.coefficient, w.kPlus_pos,
    w.kPlus_lt, w.kMinus_pos, w.kMinus_lt]

/-- Fixing an orientation and quotient coefficient forces the carrier to
divide one of the two neighboring integers `Q*k ± 1`. -/
theorem ComplementaryPair.carrier_dvd_coefficientTarget
    {Q b : ℕ} (w : ComplementaryPair Q b) (s : Orientation) :
    match s with
    | .plus => b ∣ Q * w.coefficient s + 1
    | .minus => b ∣ Q * w.coefficient s - 1 := by
  cases s with
  | plus =>
      refine ⟨w.cPlus, ?_⟩
      simpa [ComplementaryPair.coefficient] using w.plus_eq.symm
  | minus =>
      refine ⟨w.cMinus, ?_⟩
      simp only [ComplementaryPair.coefficient]
      rw [← w.minus_eq]
      simp

/-- The coefficient target is uniformly below `Q²+1` when the carrier is
below the current stage. -/
theorem ComplementaryPair.coefficientTarget_lt_sq_add_one
    {Q b : ℕ} (w : ComplementaryPair Q b) (hbQ : b < Q)
    (s : Orientation) :
    match s with
    | .plus => Q * w.coefficient s + 1 < Q ^ 2 + 1
    | .minus => Q * w.coefficient s - 1 < Q ^ 2 + 1 := by
  have hkQ : w.coefficient s < Q :=
    lt_trans (coefficient_pos_lt w s).2 hbQ
  have hQpos : 0 < Q :=
    lt_trans (lt_trans w.kPlus_pos w.kPlus_lt) hbQ
  cases s with
  | plus =>
      simp only [ComplementaryPair.coefficient] at hkQ ⊢
      simpa [pow_two] using
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hkQ hQpos) 1
  | minus =>
      simp only [ComplementaryPair.coefficient] at hkQ ⊢
      exact lt_of_le_of_lt (Nat.sub_le _ _)
        (lt_trans (Nat.mul_lt_mul_of_pos_left hkQ hQpos)
          (by simp [pow_two]))

theorem inverseRepresentative_pos_lt
    {Q b : ℕ} (w : ComplementaryPair Q b) (s : Orientation) :
    0 < w.inverseRepresentative s ∧ w.inverseRepresentative s < Q := by
  cases s <;> simp [ComplementaryPair.inverseRepresentative, w.cPlus_pos,
    w.cPlus_lt, w.cMinus_pos, w.cMinus_lt]

/-- If the prime carrier lies above `Q / B`, every downwardness exception has
multiplier strictly below `B`.  This is the bounded parameter used by the
subsequent quadratic-fibre count. -/
theorem ComplementaryPair.exception_multiplier_lt
    {Q b B : ℕ} (w : ComplementaryPair Q b) (hb : b.Prime)
    (hband : Q < B * b) (s : Orientation)
    (hs : ¬b.Coprime (w.inverseRepresentative s)) :
    ∃ ell : ℕ, ell < B ∧
      w.inverseRepresentative s = ell * b ∧
      match s with
      | .plus => ell * b ^ 2 = Q * w.kPlus + 1
      | .minus => ell * b ^ 2 + 1 = Q * w.kMinus := by
  rcases w.exception_quadratic_shape hb s hs with ⟨ell, hell, hshape⟩
  refine ⟨ell, ?_, hell, hshape⟩
  exact Nat.lt_of_mul_lt_mul_right <| calc
      ell * b = w.inverseRepresentative s := hell.symm
      _ < Q := (inverseRepresentative_pos_lt w s).2
      _ < B * b := hband

def GoodOrientation.distinguishedDenominator
    {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hQ : 0 < Q) : Denominator :=
  ⟨Q * w.coefficient g.sign, Nat.mul_pos hQ (coefficient_pos_lt w g.sign).1⟩

def GoodOrientation.companionDenominator
    {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) : Denominator :=
  ⟨b * w.inverseRepresentative g.sign,
    Nat.mul_pos (lt_trans w.kPlus_pos w.kPlus_lt) (by
      cases g.sign <;> simp [ComplementaryPair.inverseRepresentative,
        w.cPlus_pos, w.cMinus_pos])⟩

/-- The distinguished reciprocal denominator factors through the current stage. -/
theorem distinguished_mem_primePowerStage
    {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hQpos : 0 < Q)
    (hcop : Q.Coprime (w.coefficient g.sign))
    (hkQ : w.coefficient g.sign < Q) :
    reciprocalResidue (g.distinguishedDenominator hQpos) ∈ primePowerStage Q := by
  have hkpos := (coefficient_pos_lt w g.sign).1
  apply annihilatorStage_mul_le_primePowerStage hkpos hkQ hcop
  simpa [GoodOrientation.distinguishedDenominator] using
    reciprocalResidue_mem_annihilatorStage (g.distinguishedDenominator hQpos)

/-- The companion reciprocal denominator is entirely lower-supported. -/
theorem companion_mem_lowerPrimePowerStage
    {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hbQ : b < Q) :
    reciprocalResidue g.companionDenominator ∈ lowerPrimePowerStage Q := by
  have hbpos : 0 < b := lt_trans w.kPlus_pos w.kPlus_lt
  have hcpos : 0 < w.inverseRepresentative g.sign := by
    cases g.sign <;> simp [ComplementaryPair.inverseRepresentative,
      w.cPlus_pos, w.cMinus_pos]
  have hcQ : w.inverseRepresentative g.sign < Q := by
    cases g.sign <;> simp [ComplementaryPair.inverseRepresentative,
      w.cPlus_lt, w.cMinus_lt]
  exact reciprocalResidue_mul_mem_lower_of_coprime_lt
    hbpos hcpos hbQ hcQ g.companion_coprime

/-- The atom observation is intrinsically the sum of its current and companion
reciprocal points, independently of the chosen orientation. -/
theorem atom_residue_eq_distinguished_add_companion
    {Q b p : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hQpos : 0 < Q) :
    (g.atom hQpos).residue =
      reciprocalResidue (g.distinguishedDenominator hQpos) +
        reciprocalResidue g.companionDenominator := by
  let a : Denominator := ⟨w.start g.sign, w.start_pos hQpos g.sign⟩
  have hsum : (g.atom hQpos).residue =
      reciprocalResidue a + reciprocalResidue (a + 1) := by
    have hne : a ≠ a + 1 := ne_of_lt (PNat.lt_add_right a 1)
    rw [Support.residue_eq_sum]
    change ∑ n ∈ ({a, a + 1} : Finset Denominator), reciprocalResidue n = _
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [hsum]
  cases hs : g.sign with
  | plus =>
      have ha : a = g.distinguishedDenominator hQpos := by
        apply Subtype.ext
        simp [a, GoodOrientation.distinguishedDenominator,
          ComplementaryPair.start, ComplementaryPair.coefficient, hs]
      have has : a + 1 = g.companionDenominator := by
        apply Subtype.ext
        calc
          ↑(a + 1) = a.1 + (1 : Denominator).1 := PNat.add_coe a 1
          _ = a.1 + 1 := by rfl
          _ = b * w.cPlus := by
            simpa [a, hs] using w.start_succ Orientation.plus
          _ = ↑g.companionDenominator := by
            simp [GoodOrientation.companionDenominator,
              ComplementaryPair.inverseRepresentative, hs]
      rw [has, ha]
  | minus =>
      have ha : a = g.companionDenominator := by
        apply Subtype.ext
        simp [a, GoodOrientation.companionDenominator,
          ComplementaryPair.start, ComplementaryPair.inverseRepresentative, hs]
      have has : a + 1 = g.distinguishedDenominator hQpos := by
        apply Subtype.ext
        calc
          ↑(a + 1) = a.1 + (1 : Denominator).1 := PNat.add_coe a 1
          _ = a.1 + 1 := by rfl
          _ = Q * w.kMinus := by
            simpa [a, hs] using w.start_succ Orientation.minus
          _ = ↑(g.distinguishedDenominator hQpos) := by
            simp [GoodOrientation.distinguishedDenominator,
              ComplementaryPair.coefficient, hs]
      rw [has, ha, add_comm]

/-- Every good signed-inverse atom factors through the canonical current stage. -/
theorem atom_factorsThroughPrimePowerStage
    {Q b p e : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hp : p.Prime) (_he : 0 < e)
    (hQ : Q = p ^ e) (hbQ : b < Q) :
    Support.FactorsThroughPrimePowerStage
      (g.atom (hQ.symm ▸ pow_pos hp.pos e)) Q := by
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  have hcop : Q.Coprime (w.coefficient g.sign) := by
    conv_lhs => rw [hQ]
    exact (hp.coprime_pow_of_not_dvd g.coefficient_unit).symm
  have hkQ : w.coefficient g.sign < Q :=
    lt_trans (coefficient_pos_lt w g.sign).2 hbQ
  change (g.atom hQpos).residue ∈ primePowerStage Q
  rw [atom_residue_eq_distinguished_add_companion]
  exact AddSubgroup.add_mem _
    (distinguished_mem_primePowerStage g hQpos hcop hkQ)
    (lowerPrimePowerStage_le Q (companion_mem_lowerPrimePowerStage g hbQ))

/-- Every good signed-inverse atom is intrinsically transverse to the lower
prime-power filtration. -/
theorem atom_filteredTransverse
    {Q b p e : ℕ} {w : ComplementaryPair Q b}
    (g : GoodOrientation p w) (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) (hbQ : b < Q) :
    (g.atom (hQ.symm ▸ pow_pos hp.pos e)).FilteredTransverse Q := by
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  have hfactor := atom_factorsThroughPrimePowerStage g hp he hQ hbQ
  refine ⟨hfactor, (Support.simpleFiberClass_ne_zero_iff hfactor).2 ?_⟩
  intro hatom
  have hcomp := companion_mem_lowerPrimePowerStage g hbQ
  have hdist : reciprocalResidue (g.distinguishedDenominator hQpos) ∈
      lowerPrimePowerStage Q := by
    have hsub := AddSubgroup.sub_mem (lowerPrimePowerStage Q) hatom hcomp
    rw [atom_residue_eq_distinguished_add_companion] at hsub
    simpa using hsub
  have hkpos := (coefficient_pos_lt w g.sign).1
  apply reciprocalResidue_primePow_mul_not_mem_lower hp he hQ hQpos hkpos
  simpa [GoodOrientation.distinguishedDenominator] using hdist

end SignedInverse
end Erdos289
