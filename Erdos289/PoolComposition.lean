module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.TransverseReservoir

@[expose] public section

/-!
# Finite composition inside a compatible physical pool

The aggregate support is the finite colimit (union) of a selected subpool.
Pairwise physical compatibility makes this union a defined iterated product in
the path-support PCM, so exact value and connected-component grade are additive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/-- Canonical union of a finite family of supports. -/
def aggregateSupport (A : Finset Support) : Support :=
  A.biUnion id

@[simp]
theorem aggregateSupport_empty : aggregateSupport ∅ = ∅ := by
  simp [aggregateSupport]

@[simp]
theorem aggregateSupport_insert (S : Support) (A : Finset Support) :
    aggregateSupport (insert S A) = S ∪ aggregateSupport A := by
  simp [aggregateSupport]

private theorem compatible_aggregate
    {c : PhysicalConstraint} {S : Support} {A : Finset Support}
    (hnot : S ∉ A)
    (hS : ∀ T ∈ A, S ≠ T → S.CompatibleFor T c) :
    S.CompatibleFor (aggregateSupport A) c := by
  constructor
  · constructor
    · rw [Finset.disjoint_left]
      intro x hxS hxA
      rcases Finset.mem_biUnion.mp hxA with ⟨T, hTA, hxT⟩
      by_cases hST : S = T
      · exact (hnot (hST ▸ hTA)).elim
      · exact (Finset.disjoint_left.mp (hS T hTA hST).1.1 hxS) hxT
    · intro x hxS y hyA hxy
      rcases Finset.mem_biUnion.mp hyA with ⟨T, hTA, hyT⟩
      by_cases hST : S = T
      · exact (hnot (hST ▸ hTA)).elim
      · exact (hS T hTA hST).1.2 x hxS y hyT hxy
  · intro x hxS y hyA
    rcases Finset.mem_biUnion.mp hyA with ⟨T, hTA, hyT⟩
    by_cases hST : S = T
    · exact (hnot (hST ▸ hTA)).elim
    · exact (hS T hTA hST).2 x hxS y hyT

/-- Pairwise compatible admissible atoms have an admissible aggregate. -/
theorem aggregateSupport_admissible
    {c : PhysicalConstraint} {A : Finset Support}
    (hadm : ∀ S ∈ A, S.Admissible smallBlockSizes c)
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c) :
    (aggregateSupport A).Admissible smallBlockSizes c := by
  induction A using Finset.induction_on with
  | empty =>
      simp [aggregateSupport, Support.Admissible, Support.HasBlockSizes,
        Support.Avoids, Support.Separated]
  | @insert S A hSA ih =>
      have hSadm : S.Admissible smallBlockSizes c := hadm S (by simp)
      have hAadm : ∀ T ∈ A, T.Admissible smallBlockSizes c := by
        intro T hT
        exact hadm T (by simp [hT])
      have hApair : (A : Set Support).Pairwise fun U V ↦ U.CompatibleFor V c :=
        hpair.mono (by intro T hT; simp [hT])
      have hSAgg : S.CompatibleFor (aggregateSupport A) c :=
        compatible_aggregate hSA (by
          intro T hT hST
          exact hpair (by simp) (by simp [hT]) hST)
      rw [aggregateSupport_insert]
      exact Support.admissible_union hSAgg.1 hSAgg.2 hSadm (ih hAadm hApair)

/-- Exact reciprocal value is additive over a compatible finite pool. -/
theorem aggregateSupport_value
    {c : PhysicalConstraint} {A : Finset Support}
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c) :
    (aggregateSupport A).value = ∑ S ∈ A, S.value := by
  induction A using Finset.induction_on with
  | empty => simp [aggregateSupport]
  | @insert S A hSA ih =>
      have hApair : (A : Set Support).Pairwise fun U V ↦ U.CompatibleFor V c :=
        hpair.mono (by intro T hT; simp [hT])
      have hSAgg : S.CompatibleFor (aggregateSupport A) c :=
        compatible_aggregate hSA (by
          intro T hT hST
          exact hpair (by simp) (by simp [hT]) hST)
      rw [aggregateSupport_insert, Support.value_union hSAgg.1.1, ih hApair]
      simp [hSA]

/-- Connected-component grade is additive over a compatible finite pool. -/
theorem aggregateSupport_grade
    {c : PhysicalConstraint} {A : Finset Support}
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c) :
    (aggregateSupport A).grade = ∑ S ∈ A, S.grade := by
  induction A using Finset.induction_on with
  | empty => simp [aggregateSupport, Support.grade]
  | @insert S A hSA ih =>
      have hApair : (A : Set Support).Pairwise fun U V ↦ U.CompatibleFor V c :=
        hpair.mono (by intro T hT; simp [hT])
      have hSAgg : S.CompatibleFor (aggregateSupport A) c :=
        compatible_aggregate hSA (by
          intro T hT hST
          exact hpair (by simp) (by simp [hT]) hST)
      rw [aggregateSupport_insert, Support.grade_union_of_graphDisjoint hSAgg.1,
        ih hApair]
      simp [hSA]

end Erdos289
