module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.CyclicRow
public import Erdos289.StageProfile

@[expose] public section

/-!
# The cyclic route to a current's local target

A pool reaches the local target of its current
(`Erdos289.CompatibleTransversePool.CoversAtGrade`) as soon as it carries two
*distinct* simple-fibre classes with enough atoms of each.  The multiplicities
are the ones exhibited by
`Erdos289.exists_multiplicities_of_two_simpleFibreClasses`: to realize the class
`x` at grade `h ≥ p`, take `k₁` atoms of the first class and `k₂ < p` of the
second, with `k₁ + k₂ = h`.

This is the mechanism the proper prime powers need, where the simple fibre is
cyclic of prime order and the fixed-cardinality fold of Dias da Silva–Hamidoune
does not apply.  It reaches the same target as the fold, so the descent does not
distinguish the two.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/--
The cyclic mechanism reaches the local target.

`Su` and `Sv` are the two stocks: disjoint subfamilies of the pool whose atoms
all have class `u`, respectively `v`, with `u ≠ v`.  The first must hold at
least `h` atoms and the second at least `p - 1`, which is exactly what the
multiplicities `k₁ ≤ h` and `k₂ < p` consume.
-/
theorem CompatibleTransversePool.coversAtGrade_of_two_classes
    {Q p e : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    {u v : PrimePowerSimpleFibre Q} (huv : u ≠ v)
    {Su Sv : Finset Support}
    (hSu : Su ⊆ P.atoms) (hSv : Sv ⊆ P.atoms) (hdisj : Disjoint Su Sv)
    (hu : ∀ S ∈ Su, P.toTransverseReservoir.classOf S = u)
    (hv : ∀ S ∈ Sv, P.toTransverseReservoir.classOf S = v)
    {h : ℕ} (hph : p ≤ h) (hcardu : h ≤ Su.card) (hcardv : p - 1 ≤ Sv.card)
    {maxMass : ℚ} (hmass : ∀ S ∈ P.atoms, S.value ≤ maxMass)
    (hgrade : ∀ S ∈ P.atoms, S.grade = 1) :
    P.CoversAtGrade h maxMass := by
  classical
  intro x
  obtain ⟨k₁, k₂, hsum, hk₂, hclass⟩ :=
    exists_multiplicities_of_two_simpleFibreClasses hp he hQ u v huv hph x
  obtain ⟨A₁, hA₁sub, hA₁card⟩ :=
    Finset.exists_subset_card_eq (show k₁ ≤ Su.card by omega)
  obtain ⟨A₂, hA₂sub, hA₂card⟩ :=
    Finset.exists_subset_card_eq (show k₂ ≤ Sv.card by omega)
  have hAdisj : Disjoint A₁ A₂ := hdisj.mono hA₁sub hA₂sub
  refine ⟨A₁ ∪ A₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset (hA₁sub.trans hSu) (hA₂sub.trans hSv)
  · rw [Finset.card_union_of_disjoint hAdisj, hA₁card, hA₂card, hsum]
  · exact P.compatible.mono (by
      intro S hS
      exact Finset.union_subset (hA₁sub.trans hSu) (hA₂sub.trans hSv) hS)
  all_goals
    have hsub : A₁ ∪ A₂ ⊆ P.atoms :=
      Finset.union_subset (hA₁sub.trans hSu) (hA₂sub.trans hSv)
    have hpair : ((A₁ ∪ A₂ : Finset Support) : Set Support).Pairwise
        fun S T ↦ S.CompatibleFor T c := P.compatible.mono (by intro S hS; exact hsub hS)
    have hcard : (A₁ ∪ A₂).card = h := by
      rw [Finset.card_union_of_disjoint hAdisj, hA₁card, hA₂card, hsum]
  · rw [aggregateSupport_grade hpair,
      Finset.sum_congr rfl fun S hS => hgrade S (hsub hS)]
    simpa using hcard
  · rw [aggregateSupport_value hpair]
    calc ∑ S ∈ A₁ ∪ A₂, S.value
        ≤ ∑ _S ∈ A₁ ∪ A₂, maxMass :=
          Finset.sum_le_sum fun S hS => hmass S (hsub hS)
      _ = (h : ℚ) * maxMass := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  · intro hfac
    have hfacs : ∀ S ∈ A₁ ∪ A₂, S.FactorsThroughPrimePowerStage Q :=
      fun S hS => Classical.choose (P.transverse S (hsub hS))
    have hkey := aggregateSupport_simpleFibreClass hpair hfacs
    rw [Support.simpleFibreClass_congr hfac (aggregateSupport_factorsThrough hpair hfacs),
      hkey]
    have hterm : ∀ S : {y // y ∈ A₁ ∪ A₂},
        S.1.simpleFibreClass (hfacs S.1 S.2)
          = P.toTransverseReservoir.classOf S.1 :=
      fun S => (P.toTransverseReservoir.classOf_eq (hsub S.2) (hfacs S.1 S.2)).symm
    rw [Finset.sum_congr rfl fun S _ => hterm S,
      Finset.sum_attach (A₁ ∪ A₂) fun S => P.toTransverseReservoir.classOf S,
      Finset.sum_union hAdisj,
      Finset.sum_congr rfl fun S hS => hu S (hA₁sub hS),
      Finset.sum_congr rfl fun S hS => hv S (hA₂sub hS),
      Finset.sum_const, Finset.sum_const, hA₁card, hA₂card]
    exact hclass

end Erdos289
