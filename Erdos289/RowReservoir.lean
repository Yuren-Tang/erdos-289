module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.RowCertificate
public import Erdos289.SignedInverseConflict

@[expose] public section

/-!
# From a row of carriers to a transverse reservoir

`Erdos289.SignedInverse.exists_rowCertificate` produces a row of carriers with
a section of the good-orientation fibration over it.  Each member of the row
has one oriented atom, the binary block at its distinguished start, and this
module assembles those atoms into a `TransverseReservoir`.

Two facts make the assembly exact rather than merely sufficient.

* The atoms of distinct row members are distinct.  The start of an oriented
  atom is `Q k` or `Q k - 1`, where `k` is the current coefficient
  (`ComplementaryPair.distinguished_le_start_succ` and
  `ComplementaryPair.start_le_distinguished`), so distinct coefficients are
  separated by at least `Q - 1 ≥ 1` and the blocks cannot coincide.  The
  reservoir therefore has exactly as many atoms as the row has members.
* The row's rank truncation places every distinguished start beyond `Q t - 1`,
  which is simultaneously admissibility beyond the constraint's obstacle cutoff
  and the mass bound `2 / (Q t - 1)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

variable {Q p : ℕ}

/-- The oriented atom of a carrier under a section, as a physical support.
The section need not be good for this to be defined; goodness enters only in
the transversality of the resulting atom. -/
noncomputable def rowStart (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation)
    (x : Carrier Q p) : Denominator :=
  ⟨(x.pair hQ1).start (σ x), (x.pair hQ1).start_pos (by omega) (σ x)⟩

theorem rowStart_val (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation)
    (x : Carrier Q p) :
    (rowStart hQ1 σ x).1 = (x.pair hQ1).start (σ x) := rfl

theorem binaryBlock_rowStart_eq_atom
    (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation) {x : Carrier Q p}
    (hgood : σ x ∈ (x.pair hQ1).goodOrientations p) :
    binaryBlock (rowStart hQ1 σ x) =
      ((x.pair hQ1).goodOrientationOfMem (σ x) hgood).atom (by omega : 0 < Q) :=
  rfl

/-- Distinct current coefficients give distinct distinguished starts: the start
is within one of `Q` times the coefficient, and `Q ≥ 2`. -/
theorem rowStart_injOn_of_coefficient_injOn
    (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation) {R : Finset (Carrier Q p)}
    (hinj : Set.InjOn (fun x : Carrier Q p ↦ (x.pair hQ1).coefficient (σ x)) R) :
    Set.InjOn (rowStart hQ1 σ) R := by
  intro x hx y hy hxy
  refine hinj hx hy ?_
  have hx1 := (x.pair hQ1).distinguished_le_start_succ (σ x)
  have hx2 := (x.pair hQ1).start_le_distinguished (σ x)
  have hy1 := (y.pair hQ1).distinguished_le_start_succ (σ y)
  have hy2 := (y.pair hQ1).start_le_distinguished (σ y)
  have hstart : (x.pair hQ1).start (σ x) = (y.pair hQ1).start (σ y) :=
    congrArg Subtype.val hxy
  set kx := (x.pair hQ1).coefficient (σ x)
  set ky := (y.pair hQ1).coefficient (σ y)
  rcases Nat.lt_trichotomy kx ky with h | h | h
  · have : Q * kx + Q ≤ Q * ky := by
      have := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt h)
      omega
    omega
  · exact h
  · have : Q * ky + Q ≤ Q * kx := by
      have := Nat.mul_le_mul_left Q (Nat.succ_le_of_lt h)
      omega
    omega

/-! ### Core-obstacle deletion -/

/--
Only boundedly many members of a row have an atom meeting the obstacle, and the
bound is twice the obstacle's size — independent of the current and of the row.

This is the whole cost of compatibility with a fixed finite core: the tail does
not have to lie beyond the core, only to delete the finitely many carriers
whose atoms meet it.
-/
theorem card_obstructed_le
    (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation) (c : PhysicalConstraint)
    (T : Finset (Carrier Q p))
    (hinj : Set.InjOn (rowStart hQ1 σ) T) :
    (T.filter fun x => ¬ Disjoint (binaryBlock (rowStart hQ1 σ x)) c.obstacle).card
      ≤ 2 * c.obstacle.card := by
  classical
  set bad := T.filter fun x => ¬ Disjoint (binaryBlock (rowStart hQ1 σ x)) c.obstacle
    with hbad
  have hne : ∀ x ∈ bad, (binaryBlock (rowStart hQ1 σ x) ∩ c.obstacle).Nonempty := by
    intro x hx
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    exact (Finset.mem_filter.mp hx).2 (Finset.disjoint_iff_inter_eq_empty.mpr hemp)
  set f : Carrier Q p → Denominator × ℕ := fun x =>
    if hx : (binaryBlock (rowStart hQ1 σ x) ∩ c.obstacle).Nonempty then
      (hx.choose, if hx.choose = rowStart hQ1 σ x then 0 else 1)
    else (rowStart hQ1 σ x, 0) with hf
  have hmaps : ∀ x ∈ bad, f x ∈ c.obstacle ×ˢ Finset.range 2 := by
    intro x hx
    have hx' := hne x hx
    simp only [hf, dif_pos hx', Finset.mem_product, Finset.mem_range]
    refine ⟨(Finset.mem_inter.mp hx'.choose_spec).2, ?_⟩
    split <;> omega
  refine le_trans (Finset.card_le_card_of_injOn f hmaps ?_) ?_
  · intro x hx y hy hxy
    have hx' := hne x hx
    have hy' := hne y hy
    simp only [hf, dif_pos hx', dif_pos hy', Prod.mk.injEq] at hxy
    have hstart : rowStart hQ1 σ x = rowStart hQ1 σ y := by
      by_cases hcx : hx'.choose = rowStart hQ1 σ x
      · have hcy : hy'.choose = rowStart hQ1 σ y := by
          by_contra hcon
          simp [hcx, hcon] at hxy
        rw [← hcx, ← hcy, hxy.1]
      · have hcy : hy'.choose ≠ rowStart hQ1 σ y := by
          intro hcon
          simp [hcx, hcon] at hxy
        -- both chosen points are the upper endpoint of their block
        have hxup : hx'.choose = rowStart hQ1 σ x + 1 := by
          rcases mem_binaryBlock.mp (Finset.mem_inter.mp hx'.choose_spec).1 with h | h
          · exact absurd h hcx
          · exact h
        have hyup : hy'.choose = rowStart hQ1 σ y + 1 := by
          rcases mem_binaryBlock.mp (Finset.mem_inter.mp hy'.choose_spec).1 with h | h
          · exact absurd h hcy
          · exact h
        have : rowStart hQ1 σ x + 1 = rowStart hQ1 σ y + 1 := by
          rw [← hxup, ← hyup, hxy.1]
        exact add_right_cancel this
    exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hstart
  · rw [Finset.card_product, Finset.card_range, Nat.mul_comm]

/--
The reservoir of a row: the binary blocks at the distinguished starts of its
members.  Admissibility and transversality are the row's own two properties,
remoteness and goodness.
-/
noncomputable def rowReservoir
    {e : ℕ} {c : PhysicalConstraint} (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation)
    (T : Finset (Carrier Q p))
    (hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p)
    (havoid : ∀ x ∈ T, (binaryBlock (rowStart hQ1 σ x)).Avoids c) :
    TransverseReservoir Q c := by
  classical
  refine
    { atoms := T.attach.image fun x ↦ binaryBlock (rowStart hQ1 σ x.1)
      admissible := ?_
      transverse := ?_ }
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
    exact binaryBlock_admissible_of_avoids c _ (havoid x.1 x.2)
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
    rw [binaryBlock_rowStart_eq_atom hQ1 σ (hgood x.1 x.2)]
    exact atom_filteredTransverse _ hp he hQ x.1.b_lt

theorem rowReservoir_atoms
    {e : ℕ} {c : PhysicalConstraint} (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation)
    (T : Finset (Carrier Q p))
    (hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p)
    (havoid : ∀ x ∈ T, (binaryBlock (rowStart hQ1 σ x)).Avoids c) :
    (rowReservoir (c := c) hp he hQ hQ1 σ T hgood havoid).atoms =
      (T.image (rowStart hQ1 σ)).image binaryBlock := by
  classical
  rw [Finset.image_image]
  refine Finset.ext fun S ↦ ?_
  simp only [rowReservoir, Finset.mem_image, Finset.mem_attach, true_and,
    Subtype.exists, Function.comp_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

theorem card_rowReservoir_atoms
    {e : ℕ} {c : PhysicalConstraint} (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation)
    (T : Finset (Carrier Q p))
    (hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p)
    (havoid : ∀ x ∈ T, (binaryBlock (rowStart hQ1 σ x)).Avoids c)
    (hinj : Set.InjOn (fun x : Carrier Q p ↦ (x.pair hQ1).coefficient (σ x)) T) :
    (rowReservoir (c := c) hp he hQ hQ1 σ T hgood havoid).atoms.card = T.card := by
  classical
  rw [rowReservoir_atoms]
  rw [Finset.card_image_of_injective _ binaryBlock_injective,
    Finset.card_image_of_injOn (rowStart_injOn_of_coefficient_injOn hQ1 σ hinj)]

/-! ### The row certificate, read as a reservoir -/

/--
The row certificate of a prime-power current, in reservoir form.

The three parameters are unchanged: the band ratio `Λ`, the coefficient-fibre
scale `d`, and the truncation rank `t`.  The reservoir's atoms are binary
blocks, one per surviving carrier, each avoiding the obstacle and of reciprocal
mass below `2 / (Q t - 1)`; and the row size that survives the four selections
is recorded exactly.

The fourth selection is core-obstacle deletion, and it costs at most twice the
obstacle's size.  The tail is not required to lie beyond the obstacle — only to
be compatible with it.
-/
theorem exists_rowReservoir
    {Λ e n d t : ℕ} {c : PhysicalConstraint}
    (hΛ : 0 < Λ) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) (hQ1 : 1 < Q)
    (A : Finset (Carrier Q p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp hQ)
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ Q p (bandBase Λ Q))
    (hscale : Q ^ 2 + 1 < (n + 1) ^ (d + 1))
    (hpos : 1 < Q * t) :
    ∃ (R : TransverseReservoir Q c) (starts : Finset Denominator),
      R.atoms = starts.image binaryBlock ∧
      A.card - 8 * (Λ - 1)
        ≤ 2 * d * (R.atoms.card + t + 2 * c.obstacle.card) ∧
      ∀ S ∈ R.atoms, S.value < 2 / ((Q * t - 1 : ℕ) : ℚ) := by
  classical
  obtain ⟨σ, Row, T₀, hTdef, hRowA, hgoodRow, hinjRow, hdedup, htrunc, hstart⟩ :=
    exists_rowCertificate (Λ := Λ) (n := n) (d := d) (t := t) hΛ hp hQ hQ1 A hA hband hscale
  have hT₀sub : T₀ ⊆ Row := hTdef ▸ Finset.filter_subset _ _
  have hinj₀ : Set.InjOn (fun x : Carrier Q p ↦ (x.pair hQ1).coefficient (σ x)) T₀ :=
    hinjRow.mono hT₀sub
  have hstartinj : Set.InjOn (rowStart hQ1 σ) T₀ :=
    rowStart_injOn_of_coefficient_injOn hQ1 σ hinj₀
  -- core-obstacle deletion
  set T := T₀.filter fun x => Disjoint (binaryBlock (rowStart hQ1 σ x)) c.obstacle
    with hTfil
  have hTsub₀ : T ⊆ T₀ := Finset.filter_subset _ _
  have hTsub : T ⊆ Row := hTsub₀.trans hT₀sub
  have hdelete : T₀.card ≤ T.card + 2 * c.obstacle.card := by
    have hsplit : T.card
        + (T₀.filter fun x =>
            ¬ Disjoint (binaryBlock (rowStart hQ1 σ x)) c.obstacle).card
        = T₀.card := by
      rw [hTfil]
      exact Finset.card_filter_add_card_filter_not _
    have hbad := card_obstructed_le hQ1 σ c T₀ hstartinj
    omega
  have hTcoeff : ∀ x ∈ T, t ≤ (x.pair hQ1).coefficient (σ x) := by
    intro x hx
    have := hTsub₀ hx
    rw [hTdef] at this
    exact (Finset.mem_filter.mp this).2
  have hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p :=
    fun x hx => hgoodRow x (hTsub hx)
  have havoid : ∀ x ∈ T, (binaryBlock (rowStart hQ1 σ x)).Avoids c :=
    fun x hx => (Finset.mem_filter.mp hx).2
  refine ⟨rowReservoir (c := c) hp he hQ hQ1 σ T hgood havoid,
    T.image (rowStart hQ1 σ), rowReservoir_atoms hp he hQ hQ1 σ T hgood havoid,
    ?_, ?_⟩
  · have hcard := card_rowReservoir_atoms (c := c) hp he hQ hQ1 σ T hgood havoid
      (hinj₀.mono hTsub₀)
    rw [hcard]
    have hchain : Row.card ≤ T.card + t + 2 * c.obstacle.card := by omega
    calc A.card - 8 * (Λ - 1) ≤ 2 * d * Row.card := hdedup
      _ ≤ 2 * d * (T.card + t + 2 * c.obstacle.card) := Nat.mul_le_mul_left _ hchain
  · intro S hS
    rw [rowReservoir_atoms hp he hQ hQ1 σ T hgood havoid] at hS
    rcases Finset.mem_image.mp hS with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    rw [binaryBlock_rowStart_eq_atom hQ1 σ (hgood x hx)]
    exact atom_value_lt_of_mem_truncation hQ1 σ (hgood x hx) (hTcoeff x hx) hpos

end SignedInverse
end Erdos289
