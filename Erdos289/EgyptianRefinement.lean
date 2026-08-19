module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PresentationComposition
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Remote separated Egyptian refinement

The public target is the constrained reciprocal fibre `UnitFractionPresentation`.
This realization module develops the arithmetic-progression prefix and the
terminating greedy tail used to inhabit that fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

def arithmeticDenominator
    (start step : Denominator) (j : ℕ) : Denominator :=
  ⟨start.1 + j * step.1, Nat.add_pos_left start.2 _⟩

@[simp]
theorem arithmeticDenominator_value
    (start step : Denominator) (j : ℕ) :
    (arithmeticDenominator start step j).1 = start.1 + j * step.1 := rfl

theorem arithmeticDenominator_injective
    (start step : Denominator) :
    Function.Injective (arithmeticDenominator start step) := by
  intro i j h
  have hv := congrArg Subtype.val h
  simp only [arithmeticDenominator_value] at hv
  exact Nat.eq_of_mul_eq_mul_right step.2 (Nat.add_left_cancel hv)

def arithmeticSupport
    (start step : Denominator) (N : ℕ) : Support :=
  (Finset.range N).image (arithmeticDenominator start step)

def arithmeticPartialValue
    (start step : Denominator) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, reciprocal (arithmeticDenominator start step j)

theorem mem_arithmeticSupport
    {start step : Denominator} {N : ℕ} {n : Denominator} :
    n ∈ arithmeticSupport start step N ↔
      ∃ j < N, n = arithmeticDenominator start step j := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨j, hj, hjn⟩
    exact ⟨j, Finset.mem_range.mp hj, hjn.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

theorem arithmeticSupport_remote
    (start step : Denominator) (N B : ℕ) (hB : B < start.1) :
    ∀ n ∈ arithmeticSupport start step N, B < n.1 := by
  intro n hn
  rcases mem_arithmeticSupport.mp hn with ⟨j, hj, rfl⟩
  simp only [arithmeticDenominator_value]
  omega

theorem arithmeticSupport_pointSeparated
    (start step : Denominator) (N margin : ℕ)
    (hstep : margin < step.1) :
    (arithmeticSupport start step N).PointSeparated margin := by
  intro x hx y hy hxy
  rcases mem_arithmeticSupport.mp hx with ⟨i, hi, rfl⟩
  rcases mem_arithmeticSupport.mp hy with ⟨j, hj, rfl⟩
  have hij : i ≠ j := by
    intro h
    exact hxy (congrArg (arithmeticDenominator start step) h)
  simp only [arithmeticDenominator_value]
  rw [Nat.dist_add_add_left, Nat.dist_mul_right]
  have hdist : 0 < Nat.dist i j := Nat.dist_pos_of_ne hij
  have hmul : step.1 ≤ Nat.dist i j * step.1 :=
    Nat.le_mul_of_pos_left step.1 hdist
  exact hstep.trans_le hmul

@[simp]
theorem arithmeticPartialValue_succ
    (start step : Denominator) (N : ℕ) :
    arithmeticPartialValue start step (N + 1) =
      arithmeticPartialValue start step N +
        reciprocal (arithmeticDenominator start step N) := by
  simpa [arithmeticPartialValue] using
    (Finset.sum_range_succ
      (fun j => reciprocal (arithmeticDenominator start step j)) N)

theorem arithmeticSupport_value
    (start step : Denominator) (N : ℕ) :
    (arithmeticSupport start step N).value =
      arithmeticPartialValue start step N := by
  unfold arithmeticSupport arithmeticPartialValue Support.value
  rw [Finset.sum_image]
  intro i _ j _ hij
  exact arithmeticDenominator_injective start step hij

theorem arithmetic_term_comparison
    (start step : Denominator) (j : ℕ) :
    1 / (((start.1 + step.1) * (j + 1) : ℕ) : ℝ) ≤
      1 / ((arithmeticDenominator start step j).1 : ℝ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast (arithmeticDenominator start step j).2
  · exact_mod_cast (show start.1 + j * step.1 ≤
        (start.1 + step.1) * (j + 1) by nlinarith)

/-- Reciprocal sums along every positive arithmetic progression are unbounded. -/
theorem exists_arithmeticPartialValue_ge
    (start step : Denominator) (q : ℚ) :
    ∃ N : ℕ, q ≤ arithmeticPartialValue start step N := by
  have hharmonic := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [Filter.tendsto_atTop_atTop] at hharmonic
  obtain ⟨N, hN⟩ := hharmonic
    ((q : ℝ) * ((start.1 + step.1 : ℕ) : ℝ))
  have hN' := hN N le_rfl
  have hfactor : (0 : ℝ) < ((start.1 + step.1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_pos_left start.2 step.1
  have hcompare :
      (1 / (((start.1 + step.1 : ℕ) : ℝ))) *
          (∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 1)) ≤
        ∑ j ∈ Finset.range N,
          1 / ((arithmeticDenominator start step j).1 : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    calc
      (1 / (((start.1 + step.1 : ℕ) : ℝ))) *
          (1 / ((j : ℝ) + 1)) =
          1 / (((start.1 + step.1 : ℕ) : ℝ) * ((j : ℝ) + 1)) := by
            rw [one_div, one_div, one_div, mul_inv]
      _ = 1 / (((start.1 + step.1) * (j + 1) : ℕ) : ℝ) := by
        norm_num
      _ ≤ 1 / ((arithmeticDenominator start step j).1 : ℝ) :=
        arithmetic_term_comparison start step j
  have hqreal : (q : ℝ) ≤
      ∑ j ∈ Finset.range N,
        1 / ((arithmeticDenominator start step j).1 : ℝ) := by
    calc
      (q : ℝ) = (1 / (((start.1 + step.1 : ℕ) : ℝ))) *
          ((q : ℝ) * ((start.1 + step.1 : ℕ) : ℝ)) := by
        field_simp
      _ ≤ (1 / (((start.1 + step.1 : ℕ) : ℝ))) *
          (∑ j ∈ Finset.range N, 1 / ((j : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hN' (by positivity)
      _ ≤ _ := hcompare
  refine ⟨N, ?_⟩
  have hcast : ((arithmeticPartialValue start step N : ℚ) : ℝ) =
      ∑ j ∈ Finset.range N,
        1 / ((arithmeticDenominator start step j).1 : ℝ) := by
    unfold arithmeticPartialValue reciprocal
    push_cast
    rfl
  rw [← hcast] at hqreal
  exact_mod_cast hqreal

def greedyDenominator (u v : ℕ) : ℕ := v ⌈/⌉ u

def greedyResidualNumerator (u v : ℕ) : ℕ :=
  u * greedyDenominator u v - v

theorem le_mul_greedyDenominator
    {u v : ℕ} (hu : 0 < u) :
    v ≤ u * greedyDenominator u v := by
  have hself : v ⌈/⌉ u ≤ v ⌈/⌉ u := le_rfl
  simpa [greedyDenominator] using (ceilDiv_le_iff_le_mul hu).mp hself

theorem greedyDenominator_pos
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    0 < greedyDenominator u v := by
  by_contra hb
  have hb0 : greedyDenominator u v = 0 := Nat.eq_zero_of_not_pos hb
  have hle := le_mul_greedyDenominator (u := u) (v := v) hu
  rw [hb0, Nat.mul_zero] at hle
  omega

theorem mul_pred_greedyDenominator_lt
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    u * (greedyDenominator u v - 1) < v := by
  have hb := greedyDenominator_pos hu hv
  by_contra h
  have hle : v ≤ u * (greedyDenominator u v - 1) := by omega
  have hceil : greedyDenominator u v ≤ greedyDenominator u v - 1 := by
    simpa [greedyDenominator] using (ceilDiv_le_iff_le_mul hu).mpr hle
  omega

theorem greedyResidualNumerator_lt
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    greedyResidualNumerator u v < u := by
  have hb := greedyDenominator_pos hu hv
  have hprev := mul_pred_greedyDenominator_lt hu hv
  have hdecomp : u * greedyDenominator u v =
      u * (greedyDenominator u v - 1) + u := by
    nth_rewrite 1 [← Nat.sub_add_cancel hb]
    rw [Nat.mul_add, Nat.mul_one]
  unfold greedyResidualNumerator
  omega

theorem greedyResidualNumerator_add
    {u v : ℕ} (hu : 0 < u) :
    greedyResidualNumerator u v + v = u * greedyDenominator u v := by
  unfold greedyResidualNumerator
  exact Nat.sub_add_cancel (le_mul_greedyDenominator hu)

def positiveDenominator (n : ℕ) (hn : 0 < n) : Denominator := ⟨n, hn⟩

/-- A sufficiently small positive rational has a separated Egyptian tail beyond
any prescribed cutoff.  The induction measure is the unreduced numerator. -/
private theorem exists_greedySeparatedTail
    (u v K margin : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hK : margin + 2 < K)
    (hsmall : (u : ℚ) / (v : ℚ) ≤ 1 / (K : ℚ)) :
    ∃ S : Support,
      S.value = (u : ℚ) / (v : ℚ) ∧
      (∀ n ∈ S, K ≤ n.1) ∧ S.PointSeparated margin := by
  induction u using Nat.strong_induction_on generalizing v K with
  | h u ih =>
      let b := greedyDenominator u v
      let w := greedyResidualNumerator u v
      have hb : 0 < b := greedyDenominator_pos hu hv
      have hmul : v ≤ u * b := le_mul_greedyDenominator hu
      have hprev : u * (b - 1) < v := mul_pred_greedyDenominator_lt hu hv
      have hwlt : w < u := greedyResidualNumerator_lt hu hv
      have hwadd : w + v = u * b := greedyResidualNumerator_add hu
      have hKpos : (0 : ℚ) < (K : ℚ) := by
        exact_mod_cast (show 0 < K by omega)
      have hvq : (0 : ℚ) < (v : ℚ) := by exact_mod_cast hv
      have huKq : (u : ℚ) * (K : ℚ) ≤ (v : ℚ) := by
        have := (div_le_div_iff₀ hvq hKpos).mp hsmall
        simpa using this
      have huK : u * K ≤ v := by exact_mod_cast huKq
      have hKb : K ≤ b := by
        by_contra h
        have hbK : b < K := by omega
        have hubK : u * b < u * K :=
          Nat.mul_lt_mul_of_pos_left hbK hu
        omega
      let db : Denominator := positiveDenominator b hb
      by_cases hw : w = 0
      · refine ⟨{db}, ?_, ?_, ?_⟩
        · have hvub : v = u * b := by omega
          rw [show ({db} : Support).value = reciprocal db by
            simp [Support.value]]
          unfold reciprocal
          change 1 / (b : ℚ) = (u : ℚ) / (v : ℚ)
          rw [hvub]
          field_simp
          push_cast
          ring
        · intro n hn
          simp only [Finset.mem_singleton] at hn
          subst n
          exact hKb
        · intro x hx y hy hxy
          simp only [Finset.mem_singleton] at hx hy
          exact (hxy (hx.trans hy.symm)).elim
      · have hwpos : 0 < w := Nat.pos_of_ne_zero hw
        let K' := b * (b - 1)
        have hbLarge : margin + 2 < b := lt_of_lt_of_le hK hKb
        have hgap : b + margin < K' := by
          dsimp [K']
          have htwo : 2 ≤ b - 1 := by omega
          have h2b : 2 * b ≤ (b - 1) * b :=
            Nat.mul_le_mul_right b htwo
          have hsum : b + margin < 2 * b := by omega
          rw [Nat.mul_comm (b - 1) b] at h2b
          exact hsum.trans_le h2b
        have hK'b : b < K' := by omega
        have hK' : margin + 2 < K' := by omega
        have htailNat : w * K' < v * b := by
          have hK'pos : 0 < K' := by omega
          have hwu : w * K' < u * K' :=
            Nat.mul_lt_mul_of_pos_right hwlt hK'pos
          have huv : u * K' < v * b := by
            dsimp [K']
            have := Nat.mul_lt_mul_of_pos_right hprev hb
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
          exact hwu.trans huv
        have htailSmall : (w : ℚ) / ((v * b : ℕ) : ℚ) ≤
            1 / (K' : ℚ) := by
          have hvbq : (0 : ℚ) < ((v * b : ℕ) : ℚ) := by
            exact_mod_cast Nat.mul_pos hv hb
          have hK'q : (0 : ℚ) < (K' : ℚ) := by
            exact_mod_cast (show 0 < K' by omega)
          rw [div_le_div_iff₀ hvbq hK'q]
          have hc : (w : ℚ) * (K' : ℚ) ≤ ((v * b : ℕ) : ℚ) := by
            exact_mod_cast htailNat.le
          simpa using hc
        obtain ⟨T, hTvalue, hTremote, hTsep⟩ :=
          ih w hwlt (v * b) K' hwpos (Nat.mul_pos hv hb) hK' htailSmall
        have hdbnot : db ∉ T := by
          intro hmem
          have := hTremote db hmem
          change K' ≤ b at this
          omega
        refine ⟨insert db T, ?_, ?_, ?_⟩
        · rw [Support.value, Finset.sum_insert hdbnot]
          change reciprocal db + T.value = (u : ℚ) / (v : ℚ)
          rw [hTvalue]
          unfold reciprocal
          change 1 / (b : ℚ) + (w : ℚ) / ((v * b : ℕ) : ℚ) =
            (u : ℚ) / (v : ℚ)
          have hwaddq : (w : ℚ) + (v : ℚ) = (u : ℚ) * (b : ℚ) := by
            exact_mod_cast hwadd
          push_cast
          field_simp
          nlinarith
        · intro n hn
          simp only [Finset.mem_insert] at hn
          rcases hn with rfl | hn
          · exact hKb
          · exact le_trans hKb (le_trans hK'b.le (hTremote n hn))
        · intro x hx y hy hxy
          simp only [Finset.mem_insert] at hx hy
          rcases hx with rfl | hx <;> rcases hy with rfl | hy
          · exact (hxy rfl).elim
          · have hyK := hTremote y hy
            change margin < Nat.dist b y.1
            rw [Nat.dist_eq_sub_of_le (by omega)]
            omega
          · have hxK := hTremote x hx
            change margin < Nat.dist x.1 b
            rw [Nat.dist_eq_sub_of_le_right (by omega)]
            omega
          · exact hTsep x hx y hy hxy

theorem arithmeticSupport_cross_tail
    (start step : Denominator) (J margin : ℕ) (T : Support)
    (hstep : margin < step.1)
    (hremote : ∀ n ∈ T,
      (arithmeticDenominator start step J).1 ≤ n.1) :
    (arithmeticSupport start step J).CrossSeparated T margin := by
  intro x hx y hy
  rcases mem_arithmeticSupport.mp hx with ⟨i, hi, rfl⟩
  have hyremote := hremote y hy
  simp only [arithmeticDenominator_value] at hyremote ⊢
  have hisucc : i + 1 ≤ J := by omega
  have hmul : (i + 1) * step.1 ≤ J * step.1 :=
    Nat.mul_le_mul_right step.1 hisucc
  have hxgap : start.1 + i * step.1 + step.1 ≤
      start.1 + J * step.1 := by
    calc
      start.1 + i * step.1 + step.1 =
          start.1 + (i + 1) * step.1 := by
        rw [Nat.add_mul]
        omega
      _ ≤ start.1 + J * step.1 := Nat.add_le_add_left hmul start.1
  rw [Nat.dist_eq_sub_of_le (by omega)]
  omega

theorem pointSeparated_union_of_cross
    {S T : Support} {margin : ℕ}
    (hS : S.PointSeparated margin) (hT : T.PointSeparated margin)
    (hcross : S.CrossSeparated T margin) :
    (S ∪ T).PointSeparated margin := by
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hxS | hxT <;>
    rcases Finset.mem_union.mp hy with hyS | hyT
  · exact hS x hxS y hyS hxy
  · exact hcross x hxS y hyT
  · rw [Nat.dist_comm]
    exact hcross y hyS x hxT
  · exact hT x hxT y hyT hxy

/-- Every positive rational has a coefficient-one presentation beyond an
arbitrary finite cutoff and with arbitrary pairwise spacing. -/
theorem separatedEgyptianPresentation
    (q : ℚ) (hq : 0 < q) (B margin : ℕ) :
    ∃ S : Support, S.value = q ∧
      (∀ n ∈ S, B < n.1) ∧ S.PointSeparated margin := by
  let start : Denominator := ⟨B + margin + 4, by omega⟩
  let step : Denominator := ⟨margin + 1, by omega⟩
  let hex : ∃ N : ℕ, q ≤ arithmeticPartialValue start step N :=
    exists_arithmeticPartialValue_ge start step q
  let N := Nat.find hex
  have hNspec : q ≤ arithmeticPartialValue start step N := Nat.find_spec hex
  have hNpos : 0 < N := by
    by_contra h
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos h
    rw [hN0] at hNspec
    simp [arithmeticPartialValue] at hNspec
    linarith
  let J := N - 1
  have hNJ : N = J + 1 := by
    dsimp [J]
    omega
  have hJlt : J < N := by omega
  have hbefore : arithmeticPartialValue start step J < q := by
    exact lt_of_not_ge (Nat.find_min hex hJlt)
  have hcrossing : q ≤ arithmeticPartialValue start step J +
      reciprocal (arithmeticDenominator start step J) := by
    rw [← arithmeticPartialValue_succ, ← hNJ]
    exact hNspec
  let r : ℚ := q - arithmeticPartialValue start step J
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hrsmall : r ≤ reciprocal (arithmeticDenominator start step J) := by
    dsimp [r]
    linarith
  let u : ℕ := r.num.natAbs
  let v : ℕ := r.den
  have huInt : (u : ℤ) = r.num := by
    exact Int.natAbs_of_nonneg (Rat.num_pos.mpr hrpos).le
  have hu : 0 < u := by
    dsimp [u]
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hrpos))
  have hv : 0 < v := r.den_pos
  have hrepr : (u : ℚ) / (v : ℚ) = r := by
    have huQ : (u : ℚ) = (r.num : ℚ) := by exact_mod_cast huInt
    rw [huQ]
    exact r.num_div_den
  let K := (arithmeticDenominator start step J).1
  have hKlarge : margin + 2 < K := by
    change margin + 2 < (arithmeticDenominator start step J).1
    rw [arithmeticDenominator_value]
    dsimp [start]
    omega
  have hsmall : (u : ℚ) / (v : ℚ) ≤ 1 / (K : ℚ) := by
    rw [hrepr]
    simpa [reciprocal, K] using hrsmall
  obtain ⟨T, hTvalue, hTremote, hTsep⟩ :=
    exists_greedySeparatedTail u v K margin hu hv hKlarge hsmall
  let P := arithmeticSupport start step J
  have hPsep : P.PointSeparated margin := by
    exact arithmeticSupport_pointSeparated start step J margin (by
      dsimp [step]
      omega)
  have hcrossPT : P.CrossSeparated T margin := by
    exact arithmeticSupport_cross_tail start step J margin T (by
      dsimp [step]
      omega) hTremote
  have hdisj : Disjoint P T := by
    rw [Finset.disjoint_left]
    intro x hxP hxT
    have := hcrossPT x hxP x hxT
    simp at this
  refine ⟨P ∪ T, ?_, ?_, pointSeparated_union_of_cross hPsep hTsep hcrossPT⟩
  · rw [Support.value_union hdisj]
    rw [arithmeticSupport_value, hTvalue, hrepr]
    dsimp [r]
    ring
  · intro n hn
    rcases Finset.mem_union.mp hn with hnP | hnT
    · exact arithmeticSupport_remote start step J B (by
        dsimp [start]
        omega) n hnP
    · have hnK := hTremote n hnT
      have hBK : B < K := by
        change B < (arithmeticDenominator start step J).1
        rw [arithmeticDenominator_value]
        dsimp [start]
        omega
      omega

/-- Every constrained unit-fraction presentation fibre is inhabited, by the
remote arithmetic-prefix/greedy-tail construction. -/
theorem unitFractionRefinementCofinality : UnitFractionRefinementCofinality := by
  intro n c
  have hnq : (0 : ℚ) < reciprocal n := by
    unfold reciprocal
    have : (0 : ℚ) < (n.1 : ℚ) := by exact_mod_cast n.2
    positivity
  obtain ⟨S, hvalue, hremote, hsep⟩ := separatedEgyptianPresentation
    (reciprocal n) hnq c.obstacleCutoff c.separation
  refine ⟨{
    support := S
    value_eq := hvalue
    avoids := ?_
    pointSeparated := hsep }⟩
  rw [Support.Avoids, Finset.disjoint_left]
  intro x hxS hxc
  have hxcut := c.le_obstacleCutoff hxc
  exact (not_lt_of_ge hxcut) (hremote x hxS)

end Erdos289
