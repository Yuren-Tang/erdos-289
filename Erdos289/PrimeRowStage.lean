module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.RowReservoir
public import Erdos289.PrimeRowFibre
public import Erdos289.ChunkPartition
public import Erdos289.StageToTail

@[expose] public section

/-!
# A prime current: from the row certificate to a tail stage

At a prime current `Q = p` the four steps compose without loss.

1. `Erdos289.SignedInverse.exists_rowReservoir` turns the row certificate into
   a reservoir of binary atoms, all remote and all light.
2. `Erdos289.SignedInverse.card_simpleValues_rowReservoir` says the reservoir's
   image in the simple fibre is as large as the reservoir itself: distinct
   coefficients give distinct classes
   (`Erdos289.SignedInverse.atom_simpleFibreClass_ne_of_coefficient_ne`), and
   the row certificate's coefficients are pairwise distinct.
3. `Erdos289.exists_compatiblePool_of_binary_of_card` packs the reservoir into
   a compatible pool, losing at most the per-chunk capacity
   `2Δ = 4 (max 1 separation + 1)`, which depends on the constraint alone.
4. `Erdos289.tailStage_of_pool` reads the pool as one link of the tail chain.

The only inputs are the row-certificate parameters `Λ, d, t`, the constraint,
and the two comparisons that say the surviving row is large enough: large
enough to pack, and large enough for the Dias da Silva–Hamidoune interval to
contain the requested grade.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Asymptotics

namespace Erdos289
namespace SignedInverse

/-- At a prime current the atoms of a deduplicated row have pairwise distinct
simple-fibre classes. -/
theorem rowReservoir_transverseClass_injective
    {p : ℕ} {c : PhysicalConstraint}
    (hp : p.Prime) (hQ1 : 1 < p) (σ : Carrier p p → Orientation)
    (T : Finset (Carrier p p))
    (hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p)
    (havoid : ∀ x ∈ T, (binaryBlock (rowStart hQ1 σ x)).Avoids c)
    (hinj : Set.InjOn (fun x : Carrier p p ↦ (x.pair hQ1).coefficient (σ x)) T) :
    ∀ S, ∀ hS : S ∈ (rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hQ1 σ T
        hgood havoid).atoms,
      ∀ T', ∀ hT' : T' ∈ (rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hQ1 σ T
        hgood havoid).atoms,
      S.transverseClass ((rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hQ1 σ T
          hgood havoid).transverse S hS)
        = T'.transverseClass ((rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hQ1
          σ T hgood havoid).transverse T' hT') → S = T' := by
  classical
  set R := rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hQ1 σ T hgood havoid
    with hRdef
  have hatoms : R.atoms = (T.image (rowStart hQ1 σ)).image binaryBlock :=
    rowReservoir_atoms hp Nat.one_pos (pow_one p).symm hQ1 σ T hgood havoid
  have hkey : ∀ S ∈ R.atoms, ∃ x ∈ T, S = binaryBlock (rowStart hQ1 σ x) := by
    intro S hS
    rw [hatoms] at hS
    rcases Finset.mem_image.mp hS with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  intro S hS T' hT' hclass
  obtain ⟨x, hx, rfl⟩ := hkey S hS
  obtain ⟨y, hy, rfl⟩ := hkey T' hT'
  by_contra hne
  have hcoeff : (x.pair hQ1).coefficient (σ x) ≠ (y.pair hQ1).coefficient (σ y) := by
    intro h
    exact hne (congrArg (fun z ↦ binaryBlock (rowStart hQ1 σ z)) (hinj hx hy h))
  -- the two presentations of an atom are definitionally the same support
  have hfacx : (((x.pair hQ1).goodOrientationOfMem (σ x)
      (hgood x hx)).atom (by omega : 0 < p)).FactorsThroughPrimePowerStage p :=
    Classical.choose (R.transverse _ hS)
  have hfacy : (((y.pair hQ1).goodOrientationOfMem (σ y)
      (hgood y hy)).atom (by omega : 0 < p)).FactorsThroughPrimePowerStage p :=
    Classical.choose (R.transverse _ hT')
  have hclass' :
      (((x.pair hQ1).goodOrientationOfMem (σ x)
          (hgood x hx)).atom (by omega : 0 < p)).simpleFibreClass hfacx
        = (((y.pair hQ1).goodOrientationOfMem (σ y)
          (hgood y hy)).atom (by omega : 0 < p)).simpleFibreClass hfacy := hclass
  exact atom_simpleFibreClass_ne_of_coefficient_ne hp _ _ (by omega) x.b_lt y.b_lt
    hcoeff hfacx hfacy hclass'

/-- Consequently the reservoir of a deduplicated prime row has an image in the
simple fibre as large as the row itself. -/
theorem card_simpleValues_rowReservoir
    {p : ℕ} {c : PhysicalConstraint}
    (hp : p.Prime) (hQ1 : 1 < p) (σ : Carrier p p → Orientation)
    (T : Finset (Carrier p p))
    (hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p)
    (havoid : ∀ x ∈ T, (binaryBlock (rowStart hQ1 σ x)).Avoids c)
    (hinj : Set.InjOn (fun x : Carrier p p ↦ (x.pair hQ1).coefficient (σ x)) T) :
    (rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hQ1 σ T hgood
      havoid).simpleValues.card = T.card := by
  classical
  rw [TransverseReservoir.card_simpleValues_of_injective _
      (rowReservoir_transverseClass_injective hp hQ1 σ T hgood havoid hinj),
    card_rowReservoir_atoms hp Nat.one_pos (pow_one p).symm hQ1 σ T hgood havoid hinj]

/-! ### The composite: a band of carriers is a tail stage -/

/--
One prime current, end to end.

From a family `A` of band carriers at the prime current `p`, large enough that
the three selections of the row certificate still leave `m` chunks' worth of
atoms, one obtains a tail stage from the lower stage to the current one, at
every grade `h` of the Dias da Silva–Hamidoune interval `[a, m - a]`, of load
at most `h · 2 / (p t - 1)`.

Every constant is a parameter: the band ratio `Λ`, the coefficient-fibre scale
`d`, the truncation rank `t`, the surviving size `m`, and the interval endpoint
`a`.  The one arithmetic input specific to this module is the supply
inequality, which says the band is large enough to survive deletion,
deduplication, truncation and packing.
-/
theorem exists_tailStage_of_band
    {Λ p n d t m a h : ℕ} {c : PhysicalConstraint}
    (hΛ : 0 < Λ) (hd : 0 < d) (hp : p.Prime) (hp1 : 1 < p)
    (A : Finset (Carrier p p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp (pow_one p).symm)
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ p p (bandBase Λ p))
    (hscale : p ^ 2 + 1 < (n + 1) ^ (d + 1))
    (hpos : 1 < p * t)
    (hm : 0 < m)
    (hsupply :
      8 * (Λ - 1)
        + 2 * d * (m * (4 * (max 1 c.separation + 1)) + t + 2 * c.obstacle.card)
        ≤ A.card)
    (hh : 0 < h) (hah : a ≤ h) (hhm : h + a ≤ m)
    (hend : p ≤ a * (m - a) + 1) :
    ∃ F : Support,
      TailStage c F (lowerPrimePowerStage p) (primePowerStage p) h
        (h * (2 / ((p * t - 1 : ℕ) : ℚ))) := by
  classical
  set K := 4 * (max 1 c.separation + 1) with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨σ, Row, T₀, hTdef, hRowA, hgoodRow, hinjRow, hdedup, htrunc, hstart⟩ :=
    exists_rowCertificate (Λ := Λ) (n := n) (d := d) (t := t) hΛ hp
      (pow_one p).symm hp1 A hA hband hscale
  have hT₀sub : T₀ ⊆ Row := hTdef ▸ Finset.filter_subset _ _
  have hinj₀ : Set.InjOn (fun x : Carrier p p ↦ (x.pair hp1).coefficient (σ x)) T₀ :=
    hinjRow.mono hT₀sub
  have hstartinj : Set.InjOn (rowStart hp1 σ) T₀ :=
    rowStart_injOn_of_coefficient_injOn hp1 σ hinj₀
  -- core-obstacle deletion
  set T := T₀.filter fun x => Disjoint (binaryBlock (rowStart hp1 σ x)) c.obstacle
    with hTfil
  have hTsub₀ : T ⊆ T₀ := Finset.filter_subset _ _
  have hTsub : T ⊆ Row := hTsub₀.trans hT₀sub
  have hdelete : T₀.card ≤ T.card + 2 * c.obstacle.card := by
    have hsplit : T.card
        + (T₀.filter fun x =>
            ¬ Disjoint (binaryBlock (rowStart hp1 σ x)) c.obstacle).card
        = T₀.card := by
      rw [hTfil]
      exact Finset.card_filter_add_card_filter_not _
    have hbad := card_obstructed_le hp1 σ c T₀ hstartinj
    omega
  have hTcoeff : ∀ x ∈ T, t ≤ (x.pair hp1).coefficient (σ x) := by
    intro x hx
    have hx₀ := hTsub₀ hx
    rw [hTdef] at hx₀
    exact (Finset.mem_filter.mp hx₀).2
  have hgood : ∀ x ∈ T, σ x ∈ (x.pair hp1).goodOrientations p :=
    fun x hx => hgoodRow x (hTsub hx)
  have havoid : ∀ x ∈ T, (binaryBlock (rowStart hp1 σ x)).Avoids c :=
    fun x hx => (Finset.mem_filter.mp hx).2
  have hinjT : Set.InjOn (fun x : Carrier p p ↦ (x.pair hp1).coefficient (σ x)) T :=
    hinj₀.mono hTsub₀
  set R := rowReservoir (c := c) hp Nat.one_pos (pow_one p).symm hp1 σ T hgood havoid
    with hRdef
  have hatoms : R.atoms = (T.image (rowStart hp1 σ)).image binaryBlock :=
    rowReservoir_atoms hp Nat.one_pos (pow_one p).symm hp1 σ T hgood havoid
  have hcardR : R.atoms.card = T.card :=
    card_rowReservoir_atoms hp Nat.one_pos (pow_one p).symm hp1 σ T hgood havoid hinjT
  -- the surviving row is large enough to pack into `m` chunks
  have hrow : m * K ≤ R.atoms.card := by
    rw [hcardR]
    have hchain : 2 * d * (m * K + t + 2 * c.obstacle.card)
        ≤ 2 * d * (T.card + t + 2 * c.obstacle.card) := by
      have h1 : A.card ≤ 2 * d * Row.card + 8 * (Λ - 1) := by omega
      have h2 : Row.card ≤ T.card + t + 2 * c.obstacle.card := by omega
      have h3 : 2 * d * Row.card ≤ 2 * d * (T.card + t + 2 * c.obstacle.card) :=
        Nat.mul_le_mul_left _ h2
      omega
    have hdpos : 0 < 2 * d := by omega
    have := Nat.le_of_mul_le_mul_left hchain hdpos
    omega
  obtain ⟨P, hPsub, hPcard⟩ :=
    exists_compatiblePool_of_binary_of_card R (T.image (rowStart hp1 σ)) hatoms
      (by rw [← hK] at *; calc K = 1 * K := (one_mul K).symm
        _ ≤ m * K := Nat.mul_le_mul_right _ hm
        _ ≤ R.atoms.card := hrow)
  have hmP : m ≤ P.atoms.card := by
    have : m * K < (P.atoms.card + 1) * K := lt_of_le_of_lt hrow hPcard
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  -- the pool's image in the simple fibre is as large as the pool
  have hfibre : P.toTransverseReservoir.simpleValues.card = P.atoms.card :=
    TransverseReservoir.card_simpleValues_of_subset R P.toTransverseReservoir hPsub
      (rowReservoir_transverseClass_injective hp hp1 σ T hgood havoid hinjT)
  have hmfib : m ≤ P.toTransverseReservoir.simpleValues.card := by omega
  -- every atom is a binary block: grade one, and light by the truncation
  have hbinary : ∀ S ∈ P.atoms, ∃ x ∈ T, S = binaryBlock (rowStart hp1 σ x) := by
    intro S hS
    have := hPsub hS
    rw [hatoms] at this
    rcases Finset.mem_image.mp this with ⟨aa, ha, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hgradeP : ∀ S ∈ P.atoms, S.grade = 1 := by
    intro S hS
    obtain ⟨x, -, rfl⟩ := hbinary S hS
    exact binaryBlock_grade _
  have hmassP : ∀ S ∈ P.atoms, S.value ≤ 2 / ((p * t - 1 : ℕ) : ℚ) := by
    intro S hS
    obtain ⟨x, hx, rfl⟩ := hbinary S hS
    rw [binaryBlock_rowStart_eq_atom hp1 σ (hgood x hx)]
    exact le_of_lt
      (atom_value_lt_of_mem_truncation hp1 σ (hgood x hx) (hTcoeff x hx) hpos)
  refine ⟨aggregateSupport P.atoms, ?_⟩
  refine tailStage_of_pool P hp Nat.one_pos (pow_one p).symm hh hah
    (by omega) ?_ hmassP hgradeP ?_
  · calc p ≤ a * (m - a) + 1 := hend
      _ ≤ a * (P.toTransverseReservoir.simpleValues.card - a) + 1 := by
          have : m - a ≤ P.toTransverseReservoir.simpleValues.card - a := by omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) 1
  · intro S hS
    exact Finset.subset_biUnion_of_mem id hS

/-! ### Every large prime current is a tail stage -/

/--
The asymptotic form of the previous theorem.

Given the comparable band, and given per-current choices of the surviving size
`m`, the truncation rank `t`, the interval endpoint `a` and the grade `h`, all
of which the caller is free to make, every sufficiently large prime current is
a tail stage — provided only that the total demand of the three selections and
the packing grows more slowly than the prime supply `Q / log Q`.

The coefficient-fibre scale is the absolute constant two
(`Erdos289.SignedInverse.scale_two_of_lt`): the band base is a fixed fraction
of the current, so its cube already beats the current's square.
-/
theorem eventually_exists_tailStage
    (band : ComparableBand) {c : PhysicalConstraint} {m t a h : ℕ → ℕ}
    (hdemand : (fun Q : ℕ => ((8 * (band.ratio - 1)
          + 2 * 2 * (m Q * (4 * (max 1 c.separation + 1)) + t Q
            + 2 * c.obstacle.card) : ℕ) : ℝ))
        =o[atTop] fun Q : ℕ => (Q : ℝ) / Real.log Q)
    (hrank : ∀ᶠ Q : ℕ in atTop, 1 < Q * t Q)
    (hm : ∀ᶠ Q : ℕ in atTop, 0 < m Q)
    (hinterval : ∀ᶠ Q : ℕ in atTop,
      0 < h Q ∧ a Q ≤ h Q ∧ h Q + a Q ≤ m Q ∧ Q ≤ a Q * (m Q - a Q) + 1) :
    ∀ᶠ Q : ℕ in atTop, Q.Prime →
      ∃ F : Support, TailStage c F (lowerPrimePowerStage Q) (primePowerStage Q)
        (h Q) (h Q * (2 / ((Q * t Q - 1 : ℕ) : ℚ))) := by
  have hΛ : 0 < band.ratio := by have := band.two_le_ratio; omega
  have hsupply := eventually_demand_le_card_carrierPrimes band hdemand
  filter_upwards [hsupply, hrank, hm, hinterval,
    eventually_gt_atTop (2 * band.ratio ^ 3), eventually_gt_atTop 1]
    with Q hQsupply hQrank hQm hQint hQbig hQ1 hQprime
  -- the demand is met by the band at this current
  set A := carrierFamily (Λ := band.ratio) (n := bandBase band.ratio Q) hQprime
    (pow_one Q).symm with hAdef
  have hAcard : A.card = (carrierPrimes band.ratio Q Q (bandBase band.ratio Q)).card :=
    card_carrierFamily hQprime (pow_one Q).symm
  have hAsupply :
      8 * (band.ratio - 1)
        + 2 * 2 * (m Q * (4 * (max 1 c.separation + 1)) + t Q
          + 2 * c.obstacle.card) ≤ A.card := by
    rw [hAcard]
    exact hQsupply Q
  refine exists_tailStage_of_band (Λ := band.ratio) (n := bandBase band.ratio Q)
    (d := 2) (t := t Q) (m := m Q) (a := a Q) (h := h Q)
    hΛ (by norm_num) hQprime hQ1 A (Finset.Subset.refl _)
    (fun x hx => Carrier.mem_carrierFamily_b hQprime (pow_one Q).symm hx)
    (scale_two_of_lt hΛ hQbig) hQrank hQm hAsupply
    hQint.1 hQint.2.1 hQint.2.2.1 hQint.2.2.2

end SignedInverse
end Erdos289
