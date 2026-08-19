module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.ConflictDegree
public import Erdos289.IndependentTransversal

@[expose] public section

/-!
# From a bounded-degree reservoir to a compatible pool

The conflict graph of a transverse reservoir has the atoms as vertices and
physical incompatibility as adjacency.  `Erdos289/ConflictDegree.lean` bounds
its degree by a constant for a reservoir of binary atoms, and the packing leaf
turns any partition of a bounded-degree graph into sufficiently thick chunks
into an independent one-per-chunk section.

The section is exactly a globally compatible pool, so this module is the step
that converts the raw row into the `CompatibleTransversePool` the descent
consumes.  Nothing here needs the arithmetic origin of the atoms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- Physical compatibility is symmetric. -/
theorem Support.CompatibleFor.symm {S T : Support} {c : PhysicalConstraint}
    (h : S.CompatibleFor T c) : T.CompatibleFor S c := by
  refine ⟨h.1.symm, ?_⟩
  intro x hx y hy
  rw [Nat.dist_comm]
  exact h.2 y hy x hx

namespace TransverseReservoir

variable {Q : ℕ} {c : PhysicalConstraint}

/-- The conflict graph of a reservoir: incompatibility between distinct atoms. -/
def conflictGraph (R : TransverseReservoir Q c) :
    SimpleGraph {S : Support // S ∈ R.atoms} where
  Adj x y := x ≠ y ∧ ¬ x.1.CompatibleFor y.1 c
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hcompat => h.2 hcompat.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable instance (R : TransverseReservoir Q c) :
    DecidableRel R.conflictGraph.Adj :=
  Classical.decRel _

theorem conflictGraph_adj (R : TransverseReservoir Q c)
    (x y : {S : Support // S ∈ R.atoms}) :
    R.conflictGraph.Adj x y ↔ x ≠ y ∧ ¬ x.1.CompatibleFor y.1 c :=
  Iff.rfl

/-- A vertex degree in the conflict graph is a conflict-neighbourhood size. -/
theorem conflictGraph_degree_le (R : TransverseReservoir Q c)
    (x : {S : Support // S ∈ R.atoms}) :
    R.conflictGraph.degree x ≤ (R.conflictNeighbors x.1).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn Subtype.val ?_ ?_
  · intro y hy
    have hadj : R.conflictGraph.Adj x y := by
      simpa using (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    refine Finset.mem_filter.mpr ⟨y.2, ?_, hadj.2⟩
    intro hval
    exact hadj.1 (Subtype.ext hval).symm
  · intro u _ v _ huv
    exact Subtype.ext huv

/-- The conflict graph of a reservoir of binary atoms has constant degree. -/
theorem conflictGraph_maxDegree_le_of_binary (R : TransverseReservoir Q c)
    (starts : Finset Denominator) (hatoms : R.atoms = starts.image binaryBlock) :
    R.conflictGraph.maxDegree ≤ 2 * (max 1 c.separation + 1) := by
  classical
  refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun x => ?_
  obtain ⟨a, -, hax⟩ : ∃ a ∈ starts, binaryBlock a = x.1 := by
    have hx : x.1 ∈ starts.image binaryBlock := by
      rw [← hatoms]
      exact x.2
    exact Finset.mem_image.mp hx
  have hbound := conflictNeighbors_card_le_of_binary R starts hatoms a
  rw [hax] at hbound
  exact le_trans (conflictGraph_degree_le R x) hbound

end TransverseReservoir

/--
An independent one-per-chunk section of the conflict graph is a globally
compatible transverse pool.
-/
noncomputable def compatiblePoolOfChunkFeasible
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    {I : Type*} (pools : I → Finset {S : Support // S ∈ R.atoms})
    (f : IndependentTransversal.ChunkFeasible R.conflictGraph pools) :
    CompatibleTransversePool Q c := by
  classical
  letI : Fintype f.1 := Fintype.ofFinite f.1
  refine
    { atoms := f.1.toFinset.image Subtype.val
      admissible := ?_
      transverse := ?_
      compatible := ?_ }
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
    exact R.admissible x.1 x.2
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
    exact R.transverse x.1 x.2
  · intro S hS T hT hST
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Set.mem_toFinset] at hS hT
    obtain ⟨x, hx, rfl⟩ := hS
    obtain ⟨y, hy, rfl⟩ := hT
    have hxy : x ≠ y := fun h => hST (by rw [h])
    have hnadj : ¬ R.conflictGraph.Adj x y := f.2.1 hx hy hxy
    by_contra hcompat
    exact hnadj ⟨hxy, hcompat⟩

theorem atoms_subset_compatiblePoolOfChunkFeasible
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    {I : Type*} (pools : I → Finset {S : Support // S ∈ R.atoms})
    (f : IndependentTransversal.ChunkFeasible R.conflictGraph pools) :
    (compatiblePoolOfChunkFeasible R pools f).atoms ⊆ R.atoms := by
  classical
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨x, -, rfl⟩
  exact x.2

theorem card_le_card_atoms_compatiblePoolOfChunkFeasible
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    {I : Type*} [Fintype I] (pools : I → Finset {S : Support // S ∈ R.atoms})
    (hdisj : ∀ i j : I, i ≠ j → Disjoint (pools i) (pools j))
    (f : IndependentTransversal.ChunkFeasible R.conflictGraph pools) :
    Fintype.card I ≤ (compatiblePoolOfChunkFeasible R pools f).atoms.card := by
  classical
  letI : Fintype f.1 := Fintype.ofFinite f.1
  have hcount := IndependentTransversal.card_le_card_chosen hdisj f
  have himg : (f.1.toFinset.image Subtype.val).card = f.1.toFinset.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hatoms : (compatiblePoolOfChunkFeasible R pools f).atoms
      = f.1.toFinset.image Subtype.val := rfl
  rw [hatoms, himg]
  exact hcount

/--
The packing leaf applied to a reservoir of binary atoms: a partition into
chunks that are thick relative to the constant conflict degree yields a
globally compatible pool, of at least as many atoms as there are chunks.

The chunk count is carried through the boundary, so downstream bounds on the
simple-fibre image follow from this theorem instead of reopening the packing.
-/
theorem exists_compatiblePool_of_binary
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    (starts : Finset Denominator) (hatoms : R.atoms = starts.image binaryBlock)
    {I : Type*} [Fintype I] (pools : I → Finset {S : Support // S ∈ R.atoms})
    (hpartition : IndependentTransversal.IsPoolPartition pools)
    (hdisj : ∀ i j : I, i ≠ j → Disjoint (pools i) (pools j))
    (hthick : ∀ i, 4 * (max 1 c.separation + 1) ≤ (pools i).card) :
    ∃ P : CompatibleTransversePool Q c,
      P.atoms ⊆ R.atoms ∧ Fintype.card I ≤ P.atoms.card := by
  classical
  have hdeg := R.conflictGraph_maxDegree_le_of_binary starts hatoms
  have hthick' : ∀ i, 2 * R.conflictGraph.maxDegree ≤ (pools i).card := by
    intro i
    calc
      2 * R.conflictGraph.maxDegree ≤ 2 * (2 * (max 1 c.separation + 1)) := by omega
      _ = 4 * (max 1 c.separation + 1) := by ring
      _ ≤ (pools i).card := hthick i
  obtain ⟨f⟩ :=
    IndependentTransversal.hasChunkPacking_of_two_mul_maxDegree_le
      R.conflictGraph pools hpartition hthick'
  exact ⟨compatiblePoolOfChunkFeasible R pools f,
    atoms_subset_compatiblePoolOfChunkFeasible R pools f,
    card_le_card_atoms_compatiblePoolOfChunkFeasible R pools hdisj f⟩

end Erdos289
