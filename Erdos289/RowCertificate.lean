module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.RowTruncation
public import Erdos289.BadCarriers

@[expose] public section

/-!
# The row certificate of a prime-power current

A row is a finite family of carriers together with a section of the
good-orientation fibration *over that family*: an orientation for each member,
required to be usable only where it is used.  No orientation is named outside
the family, and every statement below quantifies the section existentially.

Three selections cut a band down to a row, and each is parametric.

1. *Deletion* removes the carriers with no usable orientation.  A band of ratio
   `Λ` loses at most `8 (Λ - 1)` of them
   (`Erdos289.SignedInverse.card_goodCarriers_ge`).
2. *Deduplication* removes repeated current coefficients.  If the coefficient
   fibre of the band has at most `d` points for each orientation, the fibre of
   a section has at most `2 d`, and a subfamily with pairwise distinct
   coefficients retains a `2 d`-th of the band.
3. *Rank truncation* discards the coefficients below a threshold `t`, which
   costs at most `t` members (`Erdos289.SignedInverse.card_upperCoefficient_ge`).

The surviving row has pairwise distinct coefficients, all at least `t`; hence
distinguished centres at least `Q t - 1`, hence remoteness beyond any fixed
obstacle cutoff and reciprocal mass below `2 / (Q t - 1)`.

Every constant in the conclusion is one of the three parameters `Λ`, `d`, `t`,
or is quoted from a sharp structural theorem proved elsewhere.  Replacing a
parameter by another admissible value changes no statement in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-! ### Deduplication by coefficient -/

/--
The coefficient-fibre bound with the positivity side condition discharged: a
coefficient is never zero, so its oriented target is never zero either.
-/
theorem carrierFamily_coefficientFibre_card_le
    {Λ Q p e n d k : ℕ} (hp : p.Prime) (hQ : Q = p ^ e)
    (hstage : 1 < Q) (s : Orientation)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ (d + 1)) :
    ((carrierFamily (Λ := Λ) (n := n) hp hQ).filter fun x ↦
      (x.pair hstage).coefficient s = k).card ≤ d := by
  classical
  by_cases hne :
      ((carrierFamily (Λ := Λ) (n := n) hp hQ).filter fun x ↦
        (x.pair hstage).coefficient s = k).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hk : 0 < k := by
      rw [← (Finset.mem_filter.mp hx).2]
      exact (coefficient_pos_lt _ s).1
    have hQk : 2 ≤ Q * k := by
      have : 2 * 1 ≤ Q * k := Nat.mul_le_mul (by omega) hk
      omega
    have hN : 0 < coefficientTarget Q k s := by
      cases s <;> simp only [coefficientTarget] <;> omega
    exact carrierFamily_coefficientFibre_card_le_of_target_pos hp hQ hstage s hN hscale
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/--
The coefficient fibre of an arbitrary section has at most `2 d` points: at most
`d` for each of the two orientations.  Nothing is assumed about the section.
-/
theorem sectionCoefficientFibre_card_le
    {Λ Q p e n d k : ℕ} (hp : p.Prime) (hQ : Q = p ^ e) (hstage : 1 < Q)
    (σ : Carrier Q p → Orientation) (A : Finset (Carrier Q p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp hQ)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ (d + 1)) :
    (A.filter fun x ↦ (x.pair hstage).coefficient (σ x) = k).card ≤ 2 * d := by
  classical
  have hsub : (A.filter fun x ↦ (x.pair hstage).coefficient (σ x) = k) ⊆
      ((carrierFamily (Λ := Λ) (n := n) hp hQ).filter fun x ↦
          (x.pair hstage).coefficient .plus = k) ∪
        ((carrierFamily (Λ := Λ) (n := n) hp hQ).filter fun x ↦
          (x.pair hstage).coefficient .minus = k) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxA, hxk⟩
    cases hs : σ x with
    | plus =>
        exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hA hxA, by rw [← hs]; exact hxk⟩)
    | minus =>
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hA hxA, by rw [← hs]; exact hxk⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := carrierFamily_coefficientFibre_card_le (Λ := Λ) (n := n) (d := d) (k := k)
    hp hQ hstage Orientation.plus hscale
  have h2 := carrierFamily_coefficientFibre_card_le (Λ := Λ) (n := n) (d := d) (k := k)
    hp hQ hstage Orientation.minus hscale
  omega

/--
Deduplication: a subfamily with pairwise distinct coefficients retains a
`2 d`-th of the family.
-/
theorem exists_dedup_row
    {Λ Q p e n d : ℕ} (hp : p.Prime) (hQ : Q = p ^ e) (hstage : 1 < Q)
    (σ : Carrier Q p → Orientation) (A : Finset (Carrier Q p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp hQ)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ (d + 1)) :
    ∃ R ⊆ A,
      Set.InjOn (fun x : Carrier Q p ↦ (x.pair hstage).coefficient (σ x)) R ∧
      A.card ≤ 2 * d * R.card := by
  classical
  obtain ⟨R, hRA, hinj, -, hcard⟩ :=
    exists_injOn_subset A (fun x : Carrier Q p ↦ (x.pair hstage).coefficient (σ x))
      (d := 2 * d)
      (fun k _ => sectionCoefficientFibre_card_le (Λ := Λ) (n := n) hp hQ hstage σ A hA hscale)
  exact ⟨R, hRA, hinj, hcard⟩

/-! ### Consequences of the truncation -/

/-- A retained coefficient forces a remote distinguished centre. -/
theorem le_start_of_mem_truncation
    {Q p t : ℕ} (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation) {x : Carrier Q p}
    (hx : t ≤ (x.pair hQ1).coefficient (σ x)) :
    Q * t - 1 ≤ (x.pair hQ1).start (σ x) :=
  le_start_of_le_coefficient _ _ hx

/-- A retained coefficient forces a light atom. -/
theorem atom_value_lt_of_mem_truncation
    {Q p t : ℕ} (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation) {x : Carrier Q p}
    (hgood : σ x ∈ (x.pair hQ1).goodOrientations p)
    (hx : t ≤ (x.pair hQ1).coefficient (σ x)) (hpos : 1 < Q * t) :
    (((x.pair hQ1).goodOrientationOfMem (σ x) hgood).atom (by omega)).value
      < 2 / ((Q * t - 1 : ℕ) : ℚ) :=
  GoodOrientation.atom_value_lt_of_le_coefficient _ (by omega) hx hpos

/-! ### Assembly -/

/--
The row certificate of a prime-power current.

From a family `A` of band carriers one extracts a section `σ`, usable on the
retained row, and a row `T` whose coefficients are pairwise distinct and at
least `t`; hence whose distinguished centres are at least `Q t - 1`.

The three parameters are the band ratio `Λ`, the coefficient-fibre bound `d`
— valid under the scale inequality `Q² + 1 < (n+1)^(d+1)` — and the truncation
threshold `t`.  The two size inequalities are the exact costs of the three
selections: deletion, deduplication, truncation.
-/
theorem exists_rowCertificate
    {Λ p e n d t : ℕ} (hΛ : 0 < Λ) (hp : p.Prime) (hQ1 : 1 < p ^ e)
    (A : Finset (Carrier (p ^ e) p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp rfl)
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ (p ^ e) p (bandBase Λ (p ^ e)))
    (hscale : (p ^ e) ^ 2 + 1 < (n + 1) ^ (d + 1)) :
    ∃ (σ : Carrier (p ^ e) p → Orientation) (R T : Finset (Carrier (p ^ e) p)),
      T = R.filter (fun x ↦ t ≤ (x.pair hQ1).coefficient (σ x)) ∧
      R ⊆ A ∧
      (∀ x ∈ R, σ x ∈ (x.pair hQ1).goodOrientations p) ∧
      Set.InjOn
        (fun x : Carrier (p ^ e) p ↦ (x.pair hQ1).coefficient (σ x)) R ∧
      A.card - 8 * (Λ - 1) ≤ 2 * d * R.card ∧
      R.card - t ≤ T.card ∧
      (∀ x ∈ T, p ^ e * t - 1 ≤ (x.pair hQ1).start (σ x)) := by
  classical
  -- a section of the good-orientation fibration, chosen only as proof technology
  set σ : Carrier (p ^ e) p → Orientation := fun x =>
    if h : ((x.pair hQ1).goodOrientations p).Nonempty then h.choose else .plus with hσdef
  have hσgood : ∀ x : Carrier (p ^ e) p, ((x.pair hQ1).goodOrientations p).Nonempty →
      σ x ∈ (x.pair hQ1).goodOrientations p := by
    intro x hx
    rw [hσdef]
    simp only [dif_pos hx]
    exact hx.choose_spec
  have hgoodsub : goodCarriers hQ1 A ⊆ A := Finset.filter_subset _ _
  have hgood : ∀ x ∈ goodCarriers hQ1 A, ((x.pair hQ1).goodOrientations p).Nonempty :=
    fun x hx => (Finset.mem_filter.mp hx).2
  obtain ⟨R, hRG, hinj, hcard⟩ :=
    exists_dedup_row (Λ := Λ) (n := n) (d := d) hp rfl hQ1 σ (goodCarriers hQ1 A)
      (hgoodsub.trans hA) hscale
  have hdel := card_goodCarriers_ge hΛ hp hQ1 A hband
  refine ⟨σ, R, R.filter (fun x ↦ t ≤ (x.pair hQ1).coefficient (σ x)), rfl,
    hRG.trans hgoodsub, fun x hx => hσgood x (hgood x (hRG hx)), hinj, by omega,
    card_upperCoefficient_ge R _ hinj t, fun x hx => ?_⟩
  exact le_start_of_mem_truncation hQ1 σ (Finset.mem_filter.mp hx).2

end SignedInverse
end Erdos289
