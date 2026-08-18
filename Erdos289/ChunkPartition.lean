module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.ReservoirPacking

@[expose] public section

/-!
# Cutting a row into chunks

`Erdos289.exists_compatiblePool_of_binary` consumes a partition of the atoms of
a reservoir into chunks of prescribed thickness.  Producing one is pure finite
combinatorics: enumerate the atoms and cut the enumeration into consecutive
blocks of length `t`, sending the overflow into the last block.

The number of chunks is `⌊|row| / t⌋`, so a row of size `m` yields
`≥ m / t - 1` chunks; that ratio, not the cut itself, is what the aggregation
step consumes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace IndependentTransversal

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Position of a vertex in the canonical enumeration, divided by the chunk
length. -/
noncomputable def chunkIndex (t : ℕ) (v : V) : ℕ :=
  ((Fintype.equivFin V) v : ℕ) / t

/-- The chunk a vertex belongs to: its block of the enumeration, with the
overflow folded into the last block. -/
noncomputable def chunkSlot (t : ℕ) (v : V) : ℕ :=
  min (chunkIndex t v) (Fintype.card V / t - 1)

/-- The chunks themselves. -/
noncomputable def chunkPool (t : ℕ) (i : Fin (Fintype.card V / t)) : Finset V :=
  Finset.univ.filter fun v => chunkSlot t v = (i : ℕ)

theorem chunkSlot_lt {t : ℕ} (hk : 0 < Fintype.card V / t) (v : V) :
    chunkSlot (V := V) t v < Fintype.card V / t :=
  lt_of_le_of_lt (min_le_right _ _) (by omega)

theorem mem_chunkPool_iff {t : ℕ} {i : Fin (Fintype.card V / t)} {v : V} :
    v ∈ chunkPool t i ↔ chunkSlot t v = (i : ℕ) := by
  simp [chunkPool]

/-- Every chunk is at least as thick as the cut length. -/
theorem card_chunkPool_ge {t : ℕ} (ht : 0 < t) (i : Fin (Fintype.card V / t)) :
    t ≤ (chunkPool t i).card := by
  classical
  have hk : (i : ℕ) + 1 ≤ Fintype.card V / t := i.2
  have hkt : (Fintype.card V / t) * t ≤ Fintype.card V := Nat.div_mul_le_self _ _
  have hbound : ∀ j : Fin t, (i : ℕ) * t + (j : ℕ) < Fintype.card V := by
    intro j
    calc (i : ℕ) * t + (j : ℕ) < (i : ℕ) * t + t := by omega
      _ = ((i : ℕ) + 1) * t := by ring
      _ ≤ (Fintype.card V / t) * t := Nat.mul_le_mul_right t hk
      _ ≤ Fintype.card V := hkt
  set f : Fin t → V :=
    fun j => (Fintype.equivFin V).symm ⟨(i : ℕ) * t + (j : ℕ), hbound j⟩ with hf
  have hslot : ∀ j : Fin t, chunkSlot (V := V) t (f j) = (i : ℕ) := by
    intro j
    have hval : ((Fintype.equivFin V) (f j) : ℕ) = (i : ℕ) * t + (j : ℕ) := by
      rw [hf]
      simp
    have hdiv : chunkIndex (V := V) t (f j) = (i : ℕ) := by
      rw [chunkIndex, hval, Nat.mul_comm (i : ℕ) t, Nat.mul_add_div ht,
        Nat.div_eq_of_lt j.2, Nat.add_zero]
    rw [chunkSlot, hdiv]
    omega
  have hinj : Set.InjOn f ↑(Finset.univ : Finset (Fin t)) := by
    intro x _ y _ hxy
    rw [hf] at hxy
    simp only [Equiv.symm_apply_eq, Equiv.apply_symm_apply] at hxy
    have : (x : ℕ) = (y : ℕ) := by
      have := congrArg Fin.val hxy
      simpa using this
    exact Fin.ext this
  calc t = (Finset.univ : Finset (Fin t)).card := by simp
    _ ≤ (chunkPool t i).card :=
        Finset.card_le_card_of_injOn f (fun j _ => mem_chunkPool_iff.2 (hslot j)) hinj

/-- The chunks are a partition. -/
theorem isPoolPartition_chunkPool {t : ℕ} (ht : 0 < t)
    (hk : 0 < Fintype.card V / t) :
    IsPoolPartition (chunkPool (V := V) t) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    have hcard := card_chunkPool_ge (V := V) ht i
    have hi' : (chunkPool (V := V) t i : Set V) = ∅ := hi
    have hempty : chunkPool (V := V) t i = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      have hv' : v ∈ (chunkPool (V := V) t i : Set V) := hv
      rw [hi'] at hv'
      exact hv'
    rw [hempty, Finset.card_empty] at hcard
    omega
  · intro v
    refine ⟨(chunkPool (V := V) t ⟨chunkSlot t v, chunkSlot_lt hk v⟩ : Set V),
      ⟨⟨⟨chunkSlot t v, chunkSlot_lt hk v⟩, rfl⟩, ?_⟩, ?_⟩
    · exact mem_chunkPool_iff.2 rfl
    · rintro b ⟨⟨i, rfl⟩, hvb⟩
      have hslot : chunkSlot (V := V) t v = (i : ℕ) := mem_chunkPool_iff.1 hvb
      congr 1
      exact Fin.ext hslot.symm

/--
A row of `m` atoms cuts into `⌊m / t⌋` chunks of thickness at least `t`.
-/
theorem exists_chunkPoolPartition {t : ℕ} (ht : 0 < t) (hV : t ≤ Fintype.card V) :
    ∃ (k : ℕ) (pools : Fin k → Finset V),
      0 < k ∧ IsPoolPartition pools ∧ (∀ i, t ≤ (pools i).card) ∧
        Fintype.card V < (k + 1) * t := by
  have hk : 0 < Fintype.card V / t := Nat.div_pos hV ht
  refine ⟨Fintype.card V / t, chunkPool (V := V) t, hk,
    isPoolPartition_chunkPool ht hk, fun i => card_chunkPool_ge ht i, ?_⟩
  have h := Nat.div_add_mod (Fintype.card V) t
  have h2 : Fintype.card V % t < t := Nat.mod_lt _ ht
  rw [add_mul, one_mul, Nat.mul_comm (Fintype.card V / t) t]
  omega

end IndependentTransversal

/--
Leaf `P` in the form the descent consumes: a binary reservoir whose row is
merely *large enough* already carries a compatible transverse pool.  The chunk
partition is supplied by `IndependentTransversal.exists_chunkPoolPartition`, so
no partition has to be exhibited by the caller.
-/
theorem exists_compatiblePool_of_binary_of_card
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    (starts : Finset Denominator) (hatoms : R.atoms = starts.image binaryBlock)
    (hcard : 4 * (max 1 c.separation + 1) ≤ R.atoms.card) :
    Nonempty (CompatibleTransversePool Q c) := by
  classical
  have hcard' : 4 * (max 1 c.separation + 1) ≤ Fintype.card {S : Support // S ∈ R.atoms} := by
    rwa [Fintype.card_coe]
  obtain ⟨k, pools, -, hpart, hthick, -⟩ :=
    IndependentTransversal.exists_chunkPoolPartition
      (V := {S : Support // S ∈ R.atoms}) (t := 4 * (max 1 c.separation + 1))
      (by omega) hcard'
  exact exists_compatiblePool_of_binary R starts hatoms pools hpart hthick

end Erdos289
