module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.StageProfile
public import Erdos289.TailComposition

@[expose] public section

/-!
# A pool at one prime-power current is a tail stage

`Erdos289.exists_pool_state_of_class` produces a state of prescribed grade and
simple-fibre class; `Erdos289.TailStage` asks for a state of prescribed grade
whose residue matches a prescribed class modulo the lower stage.  These are the
same request, because the simple fibre *is* the quotient of the current stage
by the lower one.

This module makes that identification, so that one prime-power current becomes
one link of `Erdos289.tailStage_chain`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/--
A compatible transverse pool at the current `Q` that reaches its local target
at grade `h`, and all of whose atoms lie inside a finite footprint, is a tail
stage from the lower stage to the current one.

The hypothesis is the mechanism-independent one: no arithmetic of the current
appears, only `CompatibleTransversePool.CoversAtGrade`.
-/
theorem tailStage_of_pool
    {Q : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    {h : ℕ} {maxMass : ℚ} (hcov : P.CoversAtGrade h maxMass)
    {F : Support} (hfoot : ∀ S ∈ P.atoms, S ⊆ F) :
    TailStage c F (lowerPrimePowerStage Q) (primePowerStage Q) h (h * maxMass) := by
  classical
  intro v hv
  obtain ⟨A, hAsub, -, hApair, hAgrade, hAvalue, hAclass⟩ :=
    hcov (QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) (⟨v, hv⟩ : primePowerStage Q))
  have hfac : ∀ S ∈ A, S.FactorsThroughPrimePowerStage Q :=
    fun S hS => Classical.choose (P.transverse S (hAsub hS))
  have hagg := aggregateSupport_factorsThrough hApair hfac
  refine ⟨aggregateSupport A, ?_,
    aggregateSupport_admissible (fun S hS => P.admissible S (hAsub hS)) hApair,
    hAgrade, ?_, Support.value_nonneg _, hAvalue⟩
  · intro x hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
    exact hfoot S (hAsub hS) hxS
  · refine (simpleFibre_mk_eq_iff_sub_mem hagg hv).1 ?_
    exact hAclass hagg

/--
The same, with the local target supplied by the fixed-cardinality fold.  This
is the prime-current route; a proper prime power reaches the same target by the
cyclic structure instead, and `tailStage_of_pool` does not distinguish them.
-/
theorem tailStage_of_pool_of_restrictedFold
    {Q p e : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    {a h : ℕ} (hh : 0 < h) (hah : a ≤ h)
    (hhm : h + a ≤ P.toTransverseReservoir.simpleValues.card)
    (hend : p ≤ a * (P.toTransverseReservoir.simpleValues.card - a) + 1)
    {maxMass : ℚ} (hmass : ∀ S ∈ P.atoms, S.value ≤ maxMass)
    (hgrade : ∀ S ∈ P.atoms, S.grade = 1)
    {F : Support} (hfoot : ∀ S ∈ P.atoms, S ⊆ F) :
    TailStage c F (lowerPrimePowerStage Q) (primePowerStage Q) h (h * maxMass) :=
  tailStage_of_pool P
    (P.coversAtGrade_of_restrictedFold hp he hQ hh hah hhm hend hmass hgrade) hfoot

end Erdos289
