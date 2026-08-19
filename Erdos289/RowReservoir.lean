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
    (hremote : ∀ x ∈ T, c.obstacleCutoff < (rowStart hQ1 σ x).1) :
    TransverseReservoir Q c := by
  classical
  refine
    { atoms := T.attach.image fun x ↦ binaryBlock (rowStart hQ1 σ x.1)
      admissible := ?_
      transverse := ?_ }
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
    exact binaryBlock_admissible c _ (hremote x.1 x.2)
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
    rw [binaryBlock_rowStart_eq_atom hQ1 σ (hgood x.1 x.2)]
    exact atom_filteredTransverse _ hp he hQ x.1.b_lt

theorem rowReservoir_atoms
    {e : ℕ} {c : PhysicalConstraint} (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) (hQ1 : 1 < Q) (σ : Carrier Q p → Orientation)
    (T : Finset (Carrier Q p))
    (hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p)
    (hremote : ∀ x ∈ T, c.obstacleCutoff < (rowStart hQ1 σ x).1) :
    (rowReservoir (c := c) hp he hQ hQ1 σ T hgood hremote).atoms =
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
    (hremote : ∀ x ∈ T, c.obstacleCutoff < (rowStart hQ1 σ x).1)
    (hinj : Set.InjOn (fun x : Carrier Q p ↦ (x.pair hQ1).coefficient (σ x)) T) :
    (rowReservoir (c := c) hp he hQ hQ1 σ T hgood hremote).atoms.card = T.card := by
  classical
  rw [rowReservoir_atoms]
  rw [Finset.card_image_of_injective _ binaryBlock_injective,
    Finset.card_image_of_injOn (rowStart_injOn_of_coefficient_injOn hQ1 σ hinj)]

/-! ### The row certificate, read as a reservoir -/

/--
The row certificate of a prime-power current, in reservoir form.

The three parameters are unchanged: the band ratio `Λ`, the coefficient-fibre
scale `d`, and the truncation rank `t`.  The reservoir's atoms are binary
blocks, one per surviving carrier, all beyond the constraint's obstacle cutoff
and all of reciprocal mass below `2 / (Q t - 1)`; and the row size that
survives the three selections is recorded exactly.
-/
theorem exists_rowReservoir
    {Λ e n d t : ℕ} {c : PhysicalConstraint}
    (hΛ : 0 < Λ) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) (hQ1 : 1 < Q)
    (A : Finset (Carrier Q p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp hQ)
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ Q p (bandBase Λ Q))
    (hscale : Q ^ 2 + 1 < (n + 1) ^ (d + 1))
    (hcut : c.obstacleCutoff < Q * t - 1)
    (hpos : 1 < Q * t) :
    ∃ (R : TransverseReservoir Q c) (starts : Finset Denominator),
      R.atoms = starts.image binaryBlock ∧
      A.card - 8 * (Λ - 1) ≤ 2 * d * (R.atoms.card + t) ∧
      ∀ S ∈ R.atoms, S.value < 2 / ((Q * t - 1 : ℕ) : ℚ) := by
  classical
  obtain ⟨σ, Row, T, hTdef, hRowA, hgoodRow, hinjRow, hdedup, htrunc, hstart⟩ :=
    exists_rowCertificate (Λ := Λ) (n := n) (d := d) (t := t) hΛ hp hQ hQ1 A hA hband hscale
  have hTsub : T ⊆ Row := hTdef ▸ Finset.filter_subset _ _
  have hTcoeff : ∀ x ∈ T, t ≤ (x.pair hQ1).coefficient (σ x) := by
    intro x hx
    rw [hTdef] at hx
    exact (Finset.mem_filter.mp hx).2
  have hgood : ∀ x ∈ T, σ x ∈ (x.pair hQ1).goodOrientations p :=
    fun x hx => hgoodRow x (hTsub hx)
  have hremote : ∀ x ∈ T, c.obstacleCutoff < (rowStart hQ1 σ x).1 := by
    intro x hx
    have := hstart x hx
    rw [rowStart_val]
    omega
  refine ⟨rowReservoir (c := c) hp he hQ hQ1 σ T hgood hremote,
    T.image (rowStart hQ1 σ), rowReservoir_atoms hp he hQ hQ1 σ T hgood hremote,
    ?_, ?_⟩
  · have hcard := card_rowReservoir_atoms (c := c) hp he hQ hQ1 σ T hgood hremote
      (hinjRow.mono hTsub)
    rw [hcard]
    have : Row.card ≤ T.card + t := by omega
    calc A.card - 8 * (Λ - 1) ≤ 2 * d * Row.card := hdedup
      _ ≤ 2 * d * (T.card + t) := Nat.mul_le_mul_left _ this
  · intro S hS
    rw [rowReservoir_atoms hp he hQ hQ1 σ T hgood hremote] at hS
    rcases Finset.mem_image.mp hS with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
    rw [binaryBlock_rowStart_eq_atom hQ1 σ (hgood x hx)]
    exact atom_value_lt_of_mem_truncation hQ1 σ (hgood x hx) (hTcoeff x hx) hpos

end SignedInverse
end Erdos289
