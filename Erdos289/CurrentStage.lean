module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PaddedStage
public import Erdos289.PaddingBlocks

@[expose] public section

/-!
# A pool with its padding is a tail stage

Assembling the two halves: a compatible transverse pool at the current, and a
family of padding blocks below the current compatible with it, form a state
system that reaches the current's local target at every grade from `p - 1` on,
and hence a tail stage.

The size conditions are the expected ones and nothing else enters: the pool
must have more than `(p-1)(p-2)` atoms, so that pigeonhole yields `p - 1` of a
common class, and the padding must fit below the current.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- A pool atom and a padding block are never the same support: the first has
nonzero class and the second has class zero. -/
theorem disjoint_pool_paddingBlocks
    {Q : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    {base h : ℕ} (hbase : 0 < base) (hcut : c.obstacleCutoff < base)
    (hfit : base + h * paddingSpacing c + 1 < Q) :
    Disjoint P.atoms (paddingBlocks c base hbase h) := by
  classical
  rw [Finset.disjoint_left]
  intro S hS hpad
  obtain ⟨-, hfac, hzero, -, -, -⟩ := paddingBlocks_spec (Q := Q) c hbase hcut hfit
  exact Support.transverseClass_ne_zero (P.transverse S hS)
    (hzero S hpad (hfac S hpad))

/--
The pool together with its padding covers the current's local target at grade
`h`.
-/
theorem exists_localSystem_coversAtGrade
    {Q p e : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    {h base : ℕ} (hbase : 0 < base) (hcut : c.obstacleCutoff < base)
    (hfit : base + h * paddingSpacing c + 1 < Q)
    (hcross : ∀ S ∈ P.atoms, ∀ T ∈ paddingBlocks c base hbase h, S.CompatibleFor T c)
    (hpool : (p - 1) * (p - 2) < P.atoms.card) (hph : p - 1 ≤ h)
    {maxMass : ℚ} (hmass : ∀ S ∈ P.atoms, S.value ≤ maxMass)
    (hpadMass : 2 / (base : ℚ) ≤ maxMass)
    (hgrade : ∀ S ∈ P.atoms, S.grade = 1) :
    ∃ L : LocalStateSystem Q c,
      L.atoms = P.atoms ∪ paddingBlocks c base hbase h ∧ L.CoversAtGrade h maxMass := by
  classical
  obtain ⟨hNadm, hNfac, hNzero, hNpair, hNgrade, hNmass⟩ :=
    paddingBlocks_spec (Q := Q) c hbase hcut hfit
  set N := paddingBlocks c base hbase h with hN
  set L := (LocalStateSystem.ofPool P).adjoin N hNadm hNfac hNpair
    (fun S hS T hT => hcross S hS T hT) with hL
  have hLatoms : L.atoms = P.atoms ∪ N := rfl
  -- classes of pool atoms are nonzero
  have hnz : ∀ S ∈ (LocalStateSystem.ofPool P).atoms,
      (LocalStateSystem.ofPool P).classOf S ≠ 0 := by
    intro S hS
    rw [(LocalStateSystem.ofPool P).classOf_eq hS
      (Classical.choose (P.transverse S hS))]
    exact Support.transverseClass_ne_zero (P.transverse S hS)
  obtain ⟨u, hu, hstock⟩ :=
    (LocalStateSystem.ofPool P).exists_stock_of_card hp he hQ hnz
      (m := p - 2) (by simpa using hpool)
  classical
  set Su := (LocalStateSystem.ofPool P).atoms.filter
    fun S => (LocalStateSystem.ofPool P).classOf S = u with hSu
  have hSuSub : Su ⊆ P.atoms := Finset.filter_subset _ _
  have hSuL : Su ⊆ L.atoms := hSuSub.trans Finset.subset_union_left
  have hNL : N ⊆ L.atoms := Finset.subset_union_right
  have hclassSame : ∀ S ∈ P.atoms, L.classOf S = (LocalStateSystem.ofPool P).classOf S := by
    intro S hS
    have hSL : S ∈ L.atoms := Finset.mem_union_left _ hS
    rw [L.classOf_eq hSL (L.factors S hSL),
      (LocalStateSystem.ofPool P).classOf_eq hS (L.factors S hSL)]
  refine ⟨L, hLatoms, ?_⟩
  refine L.coversAtGrade_of_stock_and_padding hp he hQ hu hSuL hNL
    (Finset.disjoint_of_subset_left hSuSub
      (disjoint_pool_paddingBlocks P hbase hcut hfit)) ?_ ?_ hph ?_ ?_ ?_ ?_
  · intro S hS
    rw [hclassSame S (hSuSub hS)]
    exact (Finset.mem_filter.1 hS).2
  · intro S hS
    exact L.classOf_eq (hNL hS) (hNfac S hS) ▸ hNzero S hS (hNfac S hS)
  · have : p - 2 < Su.card := hstock
    omega
  · rw [hN, card_paddingBlocks]
  · intro S hS
    rcases Finset.mem_union.1 hS with hS' | hS'
    · exact hmass S hS'
    · exact le_trans (le_of_lt (hNmass S hS')) hpadMass
  · intro S hS
    rcases Finset.mem_union.1 hS with hS' | hS'
    · exact hgrade S hS'
    · exact hNgrade S hS'

/--
A pool with its padding is a tail stage at the current, from the lower stage to
the current one, at every grade from `p - 1` on.

No arithmetic of the current appears beyond the two size conditions.  In
particular nothing here distinguishes a prime current from a proper prime
power: the padding mechanism serves both.
-/
theorem exists_tailStage_of_pool_and_padding
    {Q p e : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    {h base : ℕ} (hbase : 0 < base) (hcut : c.obstacleCutoff < base)
    (hfit : base + h * paddingSpacing c + 1 < Q)
    (hcross : ∀ S ∈ P.atoms, ∀ T ∈ paddingBlocks c base hbase h, S.CompatibleFor T c)
    (hpool : (p - 1) * (p - 2) < P.atoms.card) (hph : p - 1 ≤ h)
    {maxMass : ℚ} (hmass : ∀ S ∈ P.atoms, S.value ≤ maxMass)
    (hpadMass : 2 / (base : ℚ) ≤ maxMass)
    (hgrade : ∀ S ∈ P.atoms, S.grade = 1) :
    ∃ F : Support,
      TailStage c F (lowerPrimePowerStage Q) (primePowerStage Q) h (h * maxMass) := by
  obtain ⟨L, -, hcov⟩ :=
    exists_localSystem_coversAtGrade P hp he hQ hbase hcut hfit hcross hpool hph
      hmass hpadMass hgrade
  exact ⟨aggregateSupport L.atoms,
    tailStage_of_localSystem L hcov fun S hS => Finset.subset_biUnion_of_mem id hS⟩

end Erdos289
