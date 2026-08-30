import PrimeGrowth.Chebyshev

/-!
# Leaf Π — comparable prime bands

The natural admissible dilation subtype attached to a pair of Chebyshev
constants, its inhabitance, and the two-sided cardinality law for the prime band
`(X, ΛX]`.
-/

open Filter Real

namespace Erdos289

/-- The natural admissible dilation subtype `{Λ : ℕ // 2 ≤ Λ ∧ C < c * Λ}`. -/
def AdmissibleDilation (c C : ℝ) : Type := {Λ : ℕ // 2 ≤ Λ ∧ C < c * Λ}

namespace AdmissibleDilation

variable {c C : ℝ}

/-- The underlying natural number of an admissible dilation. -/
def val (Λ : AdmissibleDilation c C) : ℕ := Λ.1

theorem two_le (Λ : AdmissibleDilation c C) : 2 ≤ Λ.val := Λ.2.1

theorem upper_lt (Λ : AdmissibleDilation c C) : C < c * Λ.val := Λ.2.2

theorem one_le (Λ : AdmissibleDilation c C) : 1 ≤ Λ.val := le_trans (by norm_num) Λ.two_le

theorem pos (Λ : AdmissibleDilation c C) : 0 < Λ.val := Λ.one_le

end AdmissibleDilation

/-- Π.5: by the Archimedean property the admissible dilation subtype is
inhabited, so its projection to the terminal object is a regular epimorphism in
the frozen `Type` setting. -/
theorem admissibleDilation_regularEpi {c C : ℝ} (hc : 0 < c) :
    Nonempty (AdmissibleDilation c C) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C / c)
  refine ⟨⟨max 2 n, le_max_left _ _, ?_⟩⟩
  have hle : (n : ℝ) ≤ ((max 2 n : ℕ) : ℝ) := by exact_mod_cast le_max_right 2 n
  have h : C / c < ((max 2 n : ℕ) : ℝ) := lt_of_lt_of_le hn hle
  rw [div_lt_iff₀ hc] at h
  linarith

/-- The prime band `(X, ΛX]`. -/
def primeBand (Λ X : ℕ) : Finset ℕ := (Finset.Ioc X (Λ * X)).filter Nat.Prime

theorem mem_primeBand {Λ X p : ℕ} :
    p ∈ primeBand Λ X ↔ X < p ∧ p ≤ Λ * X ∧ p.Prime := by
  simp only [primeBand, Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- The prime-log function accumulates exactly the band weights. -/
theorem primeLogTheta_sub_eq_sum {X Y : ℕ} (h : X ≤ Y) :
    primeLogTheta Y - primeLogTheta X =
      ∑ p ∈ (Finset.Ioc X Y).filter Nat.Prime, log p := by
  classical
  have hsub : Nat.primesLE X ⊆ Nat.primesLE Y := by
    intro p hp
    simp only [Nat.primesLE, Nat.primesBelow, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (by omega), hp.2⟩
  have hdiff : Nat.primesLE Y \ Nat.primesLE X = (Finset.Ioc X Y).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Nat.primesLE, Nat.primesBelow, Finset.mem_filter,
      Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpY, hp⟩, hnot⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hc
      exact hnot ⟨by omega, hp⟩
    · rintro ⟨⟨hXp, hpY⟩, hp⟩
      exact ⟨⟨by omega, hp⟩, fun hc ↦ by omega⟩
  rw [primeLogTheta, primeLogTheta, Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log, ← hdiff, Finset.sum_sdiff_eq_sub hsub]

/-- Every prime of the band has log weight at least `log X`. -/
theorem card_primeBand_mul_log_le {Λ X : ℕ} (hX : 1 ≤ X) (hΛ : 1 ≤ Λ) :
    ((primeBand Λ X).card : ℝ) * log X ≤ primeLogTheta (Λ * X) - primeLogTheta X := by
  classical
  have hle : X ≤ Λ * X := Nat.le_mul_of_pos_left X hΛ
  rw [primeLogTheta_sub_eq_sum hle]
  have hb : ∀ p ∈ primeBand Λ X, log (X : ℝ) ≤ log (p : ℝ) := by
    intro p hp
    obtain ⟨hXp, -, -⟩ := mem_primeBand.1 hp
    exact Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hXp.le)
  simpa [primeBand, nsmul_eq_mul] using
    Finset.card_nsmul_le_sum (primeBand Λ X) (fun p ↦ log (p : ℝ)) (log (X : ℝ)) hb

/-- Every prime of the band has log weight at most `log (ΛX)`. -/
theorem le_card_primeBand_mul_log {Λ X : ℕ} (hΛ : 1 ≤ Λ) :
    primeLogTheta (Λ * X) - primeLogTheta X ≤
      ((primeBand Λ X).card : ℝ) * log ((Λ * X : ℕ) : ℝ) := by
  classical
  have hle : X ≤ Λ * X := Nat.le_mul_of_pos_left X hΛ
  rw [primeLogTheta_sub_eq_sum hle]
  have hbound : ∀ p ∈ primeBand Λ X, log (p : ℝ) ≤ log ((Λ * X : ℕ) : ℝ) := by
    intro p hp
    obtain ⟨hXp, hpΛ, hprime⟩ := mem_primeBand.1 hp
    exact Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpΛ)
  simpa [primeBand, nsmul_eq_mul, mul_comm] using
    Finset.sum_le_card_nsmul (primeBand Λ X) (fun p ↦ log (p : ℝ))
      (log ((Λ * X : ℕ) : ℝ)) hbound

/-- The eventual two-sided linear bound also holds at the dilated index. -/
private theorem eventually_bounds_dilated (B : PrimeLogBounds) {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    ∀ᶠ X : ℕ in atTop,
      B.lower * ((Λ * X : ℕ) : ℝ) ≤ primeLogTheta (Λ * X) ∧
        primeLogTheta (Λ * X) ≤ B.upper * ((Λ * X : ℕ) : ℝ) := by
  have htend : Tendsto (fun X : ℕ ↦ Λ * X) atTop atTop :=
    tendsto_atTop_mono (fun X ↦ Nat.le_mul_of_pos_left X hΛ) tendsto_id
  exact htend.eventually B.eventually_atTop

/-- Π.5: the shell upper bound for the prime band. -/
theorem primeShell_upperBound (B : PrimeLogBounds)
    (Λ : AdmissibleDilation B.lower B.upper) :
    ∀ᶠ X : ℕ in atTop,
      ((primeBand Λ.val X).card : ℝ) ≤ B.upper * Λ.val * (X / log X) := by
  filter_upwards [eventually_bounds_dilated B Λ.one_le, eventually_ge_atTop 2] with X hX hX2
  have hX1 : 1 ≤ X := by omega
  have hlogX : 0 < log (X : ℝ) := Real.log_pos (by exact_mod_cast hX2)
  have hlow := card_primeBand_mul_log_le (Λ := Λ.val) hX1 Λ.one_le
  have hup : primeLogTheta (Λ.val * X) - primeLogTheta X ≤ B.upper * Λ.val * X := by
    have h1 := hX.2
    have h2 : (0 : ℝ) ≤ primeLogTheta X := primeLogTheta_nonneg X
    have hcast : ((Λ.val * X : ℕ) : ℝ) = (Λ.val : ℝ) * (X : ℝ) := by push_cast; ring
    rw [hcast] at h1
    nlinarith
  have hkey : ((primeBand Λ.val X).card : ℝ) * log X ≤ B.upper * Λ.val * X :=
    le_trans hlow hup
  have hform : B.upper * Λ.val * ((X : ℝ) / log X) = (B.upper * Λ.val * X) / log X := by
    ring
  rw [hform, le_div_iff₀ hlogX]
  exact hkey

/-- Π.5: the prime band has cardinality comparable to `X / log X`. -/
theorem primeBand_card_asymp (B : PrimeLogBounds)
    (Λ : AdmissibleDilation B.lower B.upper) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ᶠ X : ℕ in atTop,
        c₁ * (X / log X) ≤ ((primeBand Λ.val X).card : ℝ) ∧
          ((primeBand Λ.val X).card : ℝ) ≤ c₂ * (X / log X) := by
  have hpos : 0 < B.lower * Λ.val - B.upper := by
    have := Λ.upper_lt
    linarith
  refine ⟨(B.lower * Λ.val - B.upper) / 2, B.upper * Λ.val, by positivity, ?_, ?_⟩
  · have h1 : 0 < B.upper := lt_trans B.lower_pos B.lower_lt_upper
    have h2 : (0 : ℝ) < Λ.val := by exact_mod_cast Λ.pos
    positivity
  · filter_upwards [eventually_bounds_dilated B Λ.one_le, B.eventually_atTop,
      eventually_ge_atTop 2, eventually_ge_atTop Λ.val,
      primeShell_upperBound B Λ] with X hX hXB hX2 hXΛ hupper
    refine ⟨?_, hupper⟩
    have hX1 : 1 ≤ X := by omega
    have hlogX : 0 < log (X : ℝ) := Real.log_pos (by exact_mod_cast hX2)
    have hcast : ((Λ.val * X : ℕ) : ℝ) = (Λ.val : ℝ) * (X : ℝ) := by push_cast; ring
    have hΛne : ((Λ.val : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Λ.pos.ne'
    have hXne : ((X : ℕ) : ℝ) ≠ 0 := by
      have : X ≠ 0 := by omega
      exact_mod_cast this
    have hlogΛX : log ((Λ.val * X : ℕ) : ℝ) ≤ 2 * log (X : ℝ) := by
      rw [hcast, Real.log_mul hΛne hXne]
      have : log (Λ.val : ℝ) ≤ log (X : ℝ) :=
        Real.log_le_log (by exact_mod_cast Λ.pos) (by exact_mod_cast hXΛ)
      linarith
    have hdiff : (B.lower * Λ.val - B.upper) * X ≤
        primeLogTheta (Λ.val * X) - primeLogTheta X := by
      have h1 := hX.1
      rw [hcast] at h1
      have h3 : primeLogTheta X ≤ B.upper * X := hXB.2
      nlinarith [h1, h3]
    have hcard := le_card_primeBand_mul_log (Λ := Λ.val) (X := X) Λ.one_le
    have hcardnn : (0 : ℝ) ≤ ((primeBand Λ.val X).card : ℝ) := by positivity
    have hstep : ((primeBand Λ.val X).card : ℝ) * log ((Λ.val * X : ℕ) : ℝ)
        ≤ ((primeBand Λ.val X).card : ℝ) * (2 * log (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogΛX hcardnn
    have hform : (B.lower * Λ.val - B.upper) / 2 * ((X : ℝ) / log X)
        = ((B.lower * Λ.val - B.upper) / 2 * X) / log X := by ring
    rw [hform, div_le_iff₀ hlogX]
    linarith

end Erdos289
