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

This module assembles the exact half of the row supply (manuscript Thm 17.1).
Starting from a family of prime carriers in the comparable band, three
selections are performed, none of which introduces a chosen constant:

1. *deletion* — the carriers with no usable orientation, at most twenty-four of
   them (`Erdos289.SignedInverse.card_goodCarriers_ge`);
2. *deduplication* — carriers sharing a current coefficient, in fibres of at
   most eight points because a quadratic congruence has at most four roots and
   there are two orientations (`chosenCoefficientFiber_card_le_eight`);
3. *rank truncation* — the coefficients below half their number
   (`Erdos289.SignedInverse.card_upperCoefficient_ge`).

What survives is a row whose members have pairwise distinct coefficients, all
at least half the row's length; hence distinguished centres at least
`Q ⌊|row|/2⌋ - 1`, hence remoteness beyond any fixed obstacle cutoff and
reciprocal mass below `2 / (Q ⌊|row|/2⌋ - 1)`.

The size of the surviving row is bounded below by an *exact* linear function of
the band size, `(#band - 24 - 191) / 16`; the asymptotics of the band itself
stay in `Erdos289.SignedInverse.bandCard_isBigO`, where they belong.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-! ### A total orientation selector -/

/--
One usable orientation per carrier.  The selector is total for convenience of
statement; it is meaningful exactly on the carriers that have one, and
`chosenSign_mem` is the only fact ever used about it.
-/
noncomputable def chosenSign {Q p : ℕ} (hQ1 : 1 < Q) (x : Carrier Q p) : Orientation :=
  if h : ((x.pair hQ1).goodOrientations p).Nonempty then h.choose else .plus

theorem chosenSign_mem {Q p : ℕ} (hQ1 : 1 < Q) {x : Carrier Q p}
    (h : ((x.pair hQ1).goodOrientations p).Nonempty) :
    chosenSign hQ1 x ∈ (x.pair hQ1).goodOrientations p := by
  rw [chosenSign, dif_pos h]
  exact h.choose_spec

/-- The good orientation selected at a carrier, as a `GoodOrientation`. -/
noncomputable def chosenOrientation {Q p : ℕ} (hQ1 : 1 < Q) {x : Carrier Q p}
    (h : ((x.pair hQ1).goodOrientations p).Nonempty) :
    GoodOrientation p (x.pair hQ1) :=
  (x.pair hQ1).goodOrientationOfMem _ (chosenSign_mem hQ1 h)

theorem chosenOrientation_sign {Q p : ℕ} (hQ1 : 1 < Q) {x : Carrier Q p}
    (h : ((x.pair hQ1).goodOrientations p).Nonempty) :
    (chosenOrientation hQ1 h).sign = chosenSign hQ1 x := rfl

/-! ### Deduplication by coefficient -/

/-- The coefficient-fibre bound with the positivity side condition discharged:
a coefficient is never zero, so its oriented target is never zero either. -/
theorem carrierFamily_coefficientFiber_card_le_four'
    {Q p e n k : ℕ} (hp : p.Prime) (hQ : Q = p ^ e)
    (hstage : 1 < Q) (s : Orientation)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ 5) :
    ((carrierFamily (n := n) hp hQ).filter fun x ↦
      (x.pair hstage).coefficient s = k).card ≤ 4 := by
  classical
  by_cases hne :
      ((carrierFamily (n := n) hp hQ).filter fun x ↦
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
    exact carrierFamily_coefficientFiber_card_le_four hp hQ hstage s hN hscale
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/--
Fibres of the selected coefficient have at most eight points: four roots of the
quadratic congruence for each of the two orientations.
-/
theorem chosenCoefficientFiber_card_le_eight
    {Q p e n k : ℕ} (hp : p.Prime) (hQ : Q = p ^ e) (hstage : 1 < Q)
    (A : Finset (Carrier Q p)) (hA : A ⊆ carrierFamily (n := n) hp hQ)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ 5) :
    (A.filter fun x ↦
      (x.pair hstage).coefficient (chosenSign hstage x) = k).card ≤ 8 := by
  classical
  have hsub :
      (A.filter fun x ↦ (x.pair hstage).coefficient (chosenSign hstage x) = k) ⊆
        ((carrierFamily (n := n) hp hQ).filter fun x ↦
            (x.pair hstage).coefficient .plus = k) ∪
          ((carrierFamily (n := n) hp hQ).filter fun x ↦
            (x.pair hstage).coefficient .minus = k) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxA, hxk⟩
    have hxF : x ∈ carrierFamily (n := n) hp hQ := hA hxA
    rcases hs : chosenSign hstage x with _ | _
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxF, by rw [← hs]; exact hxk⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxF, by rw [← hs]; exact hxk⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := carrierFamily_coefficientFiber_card_le_four' (k := k) hp hQ hstage .plus hscale
  have h2 := carrierFamily_coefficientFiber_card_le_four' (k := k) hp hQ hstage .minus hscale
  omega

/-- Deduplication: a subfamily of the band with pairwise distinct coefficients
retains an eighth of it. -/
theorem exists_dedup_row
    {Q p e n : ℕ} (hp : p.Prime) (hQ : Q = p ^ e) (hstage : 1 < Q)
    (A : Finset (Carrier Q p)) (hA : A ⊆ carrierFamily (n := n) hp hQ)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ 5) :
    ∃ R ⊆ A,
      Set.InjOn (fun x : Carrier Q p ↦ (x.pair hstage).coefficient (chosenSign hstage x)) R ∧
      A.card ≤ 8 * R.card := by
  classical
  obtain ⟨R, hRA, hinj, -, hcard⟩ :=
    exists_injOn_subset A (fun x ↦ (x.pair hstage).coefficient (chosenSign hstage x))
      (d := 8) (fun k _ => chosenCoefficientFiber_card_le_eight hp hQ hstage A hA hscale)
  exact ⟨R, hRA, hinj, hcard⟩

/-! ### The row certificate -/

/-- The retained half of a deduplicated row. -/
noncomputable def truncate {Q p : ℕ} (hQ1 : 1 < Q) (R : Finset (Carrier Q p)) :
    Finset (Carrier Q p) :=
  R.filter fun x ↦ R.card / 2 ≤ (x.pair hQ1).coefficient (chosenSign hQ1 x)

theorem truncate_subset {Q p : ℕ} (hQ1 : 1 < Q) (R : Finset (Carrier Q p)) :
    truncate hQ1 R ⊆ R := Finset.filter_subset _ _

theorem card_truncate_ge {Q p : ℕ} (hQ1 : 1 < Q) (R : Finset (Carrier Q p))
    (hinj : Set.InjOn (fun x : Carrier Q p ↦ (x.pair hQ1).coefficient (chosenSign hQ1 x)) R) :
    R.card - R.card / 2 ≤ (truncate hQ1 R).card :=
  card_upperCoefficient_ge R _ hinj

/-- Every retained carrier has a remote distinguished centre. -/
theorem le_start_of_mem_truncate {Q p : ℕ} (hQ1 : 1 < Q) (R : Finset (Carrier Q p))
    {x : Carrier Q p} (hx : x ∈ truncate hQ1 R) :
    Q * (R.card / 2) - 1 ≤ (x.pair hQ1).start (chosenSign hQ1 x) :=
  le_start_of_le_coefficient _ _ (Finset.mem_filter.mp hx).2

/-- Every retained carrier carries a light atom. -/
theorem atom_value_lt_of_mem_truncate {Q p : ℕ} (hQ1 : 1 < Q)
    (R : Finset (Carrier Q p)) {x : Carrier Q p} (hx : x ∈ truncate hQ1 R)
    (hgood : ((x.pair hQ1).goodOrientations p).Nonempty)
    (hpos : 1 < Q * (R.card / 2)) :
    ((chosenOrientation hQ1 hgood).atom (by omega)).value
      < 2 / ((Q * (R.card / 2) - 1 : ℕ) : ℚ) :=
  GoodOrientation.atom_value_lt_of_le_coefficient (chosenOrientation hQ1 hgood)
    (by omega) (by
      rw [chosenOrientation_sign]
      exact (Finset.mem_filter.mp hx).2) hpos

/-! ### Assembly -/

/--
The row certificate of a prime-power current, in exact form.

From a family `A` of band carriers one extracts a row `T ⊆ A` whose members
have pairwise distinct current coefficients, all at least `|T|`-large in the
sense that each is at least half the deduplicated row's length; consequently
each has distinguished centre at least `Q ⌊·/2⌋ - 1`.

Every constant appearing here is forced: twenty-four bad carriers, eight-point
coefficient fibres, and a halving.  `#A - 24 - 191 ≤ 16 #T` is the arithmetic
of `(#A - 24) ≤ 8 #R` and `#R - ⌊#R/2⌋ ≤ #T` combined.
-/
theorem exists_rowCertificate
    {p e n : ℕ} (hp : p.Prime) (hQ1 : 1 < p ^ e)
    (A : Finset (Carrier (p ^ e) p))
    (hA : A ⊆ carrierFamily (n := n) hp rfl)
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes (p ^ e) p (bandBase (p ^ e)))
    (hscale : (p ^ e) ^ 2 + 1 < (n + 1) ^ 5) :
    ∃ (R T : Finset (Carrier (p ^ e) p)),
      T = truncate hQ1 R ∧ R ⊆ A ∧
      (∀ x ∈ R, ((x.pair hQ1).goodOrientations p).Nonempty) ∧
      Set.InjOn (fun x : Carrier (p ^ e) p ↦ (x.pair hQ1).coefficient (chosenSign hQ1 x)) R ∧
      A.card - 24 ≤ 8 * R.card ∧
      R.card - R.card / 2 ≤ T.card ∧
      (∀ x ∈ T, p ^ e * (R.card / 2) - 1 ≤ (x.pair hQ1).start (chosenSign hQ1 x)) := by
  classical
  have hgoodsub : goodCarriers hQ1 A ⊆ A := Finset.filter_subset _ _
  obtain ⟨R, hRG, hinj, hcard⟩ :=
    exists_dedup_row hp rfl hQ1 (goodCarriers hQ1 A) (hgoodsub.trans hA) hscale
  have hRA : R ⊆ A := hRG.trans hgoodsub
  have hgood : ∀ x ∈ R, ((x.pair hQ1).goodOrientations p).Nonempty := by
    intro x hx
    exact (Finset.mem_filter.mp (hRG hx)).2
  have hdel := card_goodCarriers_ge hp hQ1 A hband
  refine ⟨R, truncate hQ1 R, rfl, hRA, hgood, hinj, by omega,
    card_truncate_ge hQ1 R hinj, fun x hx => le_start_of_mem_truncate hQ1 R hx⟩

end SignedInverse
end Erdos289
