import Universal.Profile.GradeResource

import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.Closure

/-!
# Resource-bound saturation

The closure fixes the grade coordinate and weakens only the resource bound.
Its fixed points carry the reflected Minkowski tensor.
-/

open scoped Pointwise

namespace Erdos289

universe u v

variable {M : Type u} {U : Type v}
variable [AddCommMonoid M] [AddCommMonoid U] [PartialOrder U] [IsOrderedAddMonoid U]

/-- The frozen grade-fixed resource preorder. -/
def ResourceBoundLE (r s : GradeResourceLabel M U) : Prop :=
  r.1 = s.1 ∧ r.2 ≤ s.2

/-- Upward closure in the resource coordinate, with the grade held fixed. -/
def boundSaturation (A : Set (GradeResourceLabel M U)) :
    Set (GradeResourceLabel M U) :=
  {s | ∃ r ∈ A, ResourceBoundLE r s}

theorem subset_boundSaturation (A : Set (GradeResourceLabel M U)) :
    A ⊆ boundSaturation A := by
  intro r hr
  exact ⟨r, hr, rfl, le_rfl⟩

theorem boundSaturation_mono : Monotone
    (boundSaturation : Set (GradeResourceLabel M U) →
      Set (GradeResourceLabel M U)) := by
  intro A B hAB s
  rintro ⟨r, hr, hrs⟩
  exact ⟨r, hAB hr, hrs⟩

@[simp]
theorem boundSaturation_idempotent (A : Set (GradeResourceLabel M U)) :
    boundSaturation (boundSaturation A) = boundSaturation A := by
  apply Set.Subset.antisymm
  · rintro s ⟨r, ⟨q, hq, hqr⟩, hrs⟩
    exact ⟨q, hq, hqr.1.trans hrs.1, hqr.2.trans hrs.2⟩
  · exact subset_boundSaturation _

/-- The upper-closure operator underlying bound semantics. -/
def boundSaturationClosure : ClosureOperator
    (Set (GradeResourceLabel M U)) where
  toFun := boundSaturation
  monotone' := boundSaturation_mono
  le_closure' := subset_boundSaturation
  idempotent' := boundSaturation_idempotent

/-- Translation invariance gives the multiplicative nucleus inequality. -/
theorem boundSaturation_add_le (A B : Set (GradeResourceLabel M U)) :
    boundSaturation A + boundSaturation B ⊆ boundSaturation (A + B) := by
  rintro s ⟨a, ⟨a₀, ha₀, haGrade, haBound⟩,
    b, ⟨b₀, hb₀, hbGrade, hbBound⟩, rfl⟩
  refine ⟨a₀ + b₀, ⟨a₀, ha₀, b₀, hb₀, rfl⟩, ?_, ?_⟩
  · exact congrArg₂ (.+.) haGrade hbGrade
  · exact add_le_add haBound hbBound

theorem boundSaturation_add_left (A B : Set (GradeResourceLabel M U)) :
    boundSaturation (boundSaturation A + B) = boundSaturation (A + B) := by
  apply Set.Subset.antisymm
  · calc
      boundSaturation (boundSaturation A + B) ⊆
          boundSaturation (boundSaturation A + boundSaturation B) :=
        boundSaturation_mono (Set.add_subset_add_left (subset_boundSaturation B))
      _ ⊆ boundSaturation (boundSaturation (A + B)) :=
        boundSaturation_mono (boundSaturation_add_le A B)
      _ = boundSaturation (A + B) := boundSaturation_idempotent _
  · apply boundSaturation_mono
    exact Set.add_subset_add_right (subset_boundSaturation A)

theorem boundSaturation_add_right (A B : Set (GradeResourceLabel M U)) :
    boundSaturation (A + boundSaturation B) = boundSaturation (A + B) := by
  rw [add_comm, boundSaturation_add_left, add_comm]

/-- U7.3: the frozen closure laws together with the quantale nucleus inequality. -/
theorem boundSaturation_isNucleus :
    (∀ A : Set (GradeResourceLabel M U), A ⊆ boundSaturation A) ∧
    Monotone (boundSaturation : Set (GradeResourceLabel M U) →
      Set (GradeResourceLabel M U)) ∧
    (∀ A : Set (GradeResourceLabel M U),
      boundSaturation (boundSaturation A) = boundSaturation A) ∧
    (∀ A B : Set (GradeResourceLabel M U),
      boundSaturation A + boundSaturation B ⊆
      boundSaturation (A + B)) :=
  ⟨subset_boundSaturation, boundSaturation_mono,
    boundSaturation_idempotent, boundSaturation_add_le⟩

/-- The fixed points of resource-bound saturation. -/
abbrev BoundProfile (M : Type u) (U : Type v)
    [AddCommMonoid M] [AddCommMonoid U] [PartialOrder U] [IsOrderedAddMonoid U] :=
  (boundSaturationClosure (M := M) (U := U)).Closeds

noncomputable instance : CompleteLattice (BoundProfile M U) :=
  (boundSaturationClosure (M := M) (U := U)).gi.liftCompleteLattice

/-- Reflection of a raw label set into bound semantics. -/
def boundProfileReflection (A : Set (GradeResourceLabel M U)) : BoundProfile M U :=
  (boundSaturationClosure (M := M) (U := U)).toCloseds A

@[simp]
theorem boundProfileReflection_coe (A : Set (GradeResourceLabel M U)) :
    (boundProfileReflection A : Set (GradeResourceLabel M U)) = boundSaturation A :=
  rfl

/-- U7.4: reflection is left adjoint to the fixed-point inclusion. -/
theorem boundProfile_reflection (A : Set (GradeResourceLabel M U))
    (B : BoundProfile M U) :
    boundProfileReflection A ≤ B ↔ A ⊆ (B : Set (GradeResourceLabel M U)) :=
  (boundSaturationClosure (M := M) (U := U)).gi.gc _ _

/-- Reflected Minkowski tensor. -/
noncomputable instance : Add (BoundProfile M U) where
  add A B := boundProfileReflection ((A : Set _) + (B : Set _))

@[simp]
theorem boundProfile_add_coe (A B : BoundProfile M U) :
    ((A + B : BoundProfile M U) : Set (GradeResourceLabel M U)) =
      boundSaturation ((A : Set _) + (B : Set _)) :=
  rfl

noncomputable instance : Zero (BoundProfile M U) where
  zero := boundProfileReflection ({0} : Set (GradeResourceLabel M U))

@[simp]
theorem boundProfile_zero_coe :
    ((0 : BoundProfile M U) : Set (GradeResourceLabel M U)) =
      boundSaturation ({0} : Set (GradeResourceLabel M U)) :=
  rfl

noncomputable instance : AddCommMonoid (BoundProfile M U) where
  add_assoc A B C := by
    apply Subtype.ext
    change boundSaturation
      (boundSaturation ((A : Set (GradeResourceLabel M U)) + (B : Set _)) +
        (C : Set (GradeResourceLabel M U))) =
      boundSaturation ((A : Set (GradeResourceLabel M U)) +
        boundSaturation ((B : Set _) + (C : Set (GradeResourceLabel M U))))
    rw [boundSaturation_add_left, boundSaturation_add_right, add_assoc]
  zero_add A := by
    apply Subtype.ext
    change boundSaturation
      (boundSaturation ({0} : Set (GradeResourceLabel M U)) +
        (A : Set (GradeResourceLabel M U))) =
      (A : Set (GradeResourceLabel M U))
    rw [boundSaturation_add_left]
    change boundSaturation
      ((0 : Set (GradeResourceLabel M U)) + (A : Set _)) = _
    rw [zero_add]
    exact A.2.closure_eq
  add_zero A := by
    apply Subtype.ext
    change boundSaturation
      ((A : Set (GradeResourceLabel M U)) +
        boundSaturation ({0} : Set (GradeResourceLabel M U))) =
      (A : Set (GradeResourceLabel M U))
    rw [boundSaturation_add_right]
    change boundSaturation
      ((A : Set (GradeResourceLabel M U)) + (0 : Set _)) = _
    rw [add_zero]
    exact A.2.closure_eq
  add_comm A B := by
    apply Subtype.ext
    change boundSaturation
      ((A : Set (GradeResourceLabel M U)) + (B : Set (GradeResourceLabel M U))) =
      boundSaturation ((B : Set (GradeResourceLabel M U)) +
        (A : Set (GradeResourceLabel M U)))
    rw [add_comm]
  nsmul := nsmulRec

/-- Joins in the fixed-point lattice are reflected unions. -/
theorem boundProfile_sSup_coe (S : Set (BoundProfile M U)) :
    ((sSup S : BoundProfile M U) : Set (GradeResourceLabel M U)) =
      boundSaturation (⋃ A ∈ S, (A : Set (GradeResourceLabel M U))) := by
  change boundSaturation
    (sSup ((fun A : BoundProfile M U ↦
      (A : Set (GradeResourceLabel M U))) '' S)) = _
  congr 1
  ext r
  simp

theorem boundSaturation_iUnion_closure {ι : Sort*}
    (F : ι → Set (GradeResourceLabel M U)) :
    boundSaturation (⋃ i, boundSaturation (F i)) =
      boundSaturation (⋃ i, F i) := by
  exact (boundSaturationClosure (M := M) (U := U)).closure_iSup_closure F

theorem boundSaturation_iUnion₂_closure {ι : Sort*} {κ : ι → Sort*}
    (F : ∀ i, κ i → Set (GradeResourceLabel M U)) :
    boundSaturation (⋃ (i) (j), boundSaturation (F i j)) =
      boundSaturation (⋃ (i) (j), F i j) := by
  exact (boundSaturationClosure (M := M) (U := U)).closure_iSup₂_closure F

theorem boundProfile_iSup_coe {ι : Sort*} (F : ι → BoundProfile M U) :
    ((⨆ i, F i) : BoundProfile M U) =
      boundProfileReflection (⋃ i, (F i : Set (GradeResourceLabel M U))) := by
  apply Subtype.ext
  rw [boundProfileReflection_coe]
  change boundSaturation
    (sSup ((fun A : BoundProfile M U ↦
      (A : Set (GradeResourceLabel M U))) '' Set.range F)) = _
  congr 1
  ext r
  simp

theorem boundProfile_iSup₂_coe {ι : Sort*} {κ : ι → Sort*}
    (F : ∀ i, κ i → BoundProfile M U) :
    ((⨆ (i) (j), F i j) : BoundProfile M U) =
      boundProfileReflection
        (⋃ (i) (j), (F i j : Set (GradeResourceLabel M U))) := by
  rw [boundProfile_iSup_coe]
  simp_rw [boundProfile_iSup_coe]
  apply Subtype.ext
  rw [boundProfileReflection_coe]
  simp_rw [boundProfileReflection_coe]
  rw [boundSaturation_iUnion_closure]

theorem boundProfile_add_sSup_distrib (A : BoundProfile M U)
    (S : Set (BoundProfile M U)) :
    A + sSup S = ⨆ B ∈ S, A + B := by
  apply Subtype.ext
  rw [boundProfile_add_coe, boundProfile_sSup_coe,
    boundSaturation_add_right]
  change boundSaturation
    ((A : Set (GradeResourceLabel M U)) +
      (⋃ B ∈ S, (B : Set (GradeResourceLabel M U)))) =
    (((⨆ B ∈ S, A + B) : BoundProfile M U) : Set _)
  rw [boundProfile_iSup₂_coe, boundProfileReflection_coe]
  simp_rw [boundProfile_add_coe]
  rw [boundSaturation_iUnion₂_closure]
  congr 1
  exact Set.image2_iUnion₂_right (.+.) (A : Set _) fun B (_ : B ∈ S) ↦
    (B : Set (GradeResourceLabel M U))

noncomputable instance : IsAddQuantale (BoundProfile M U) where
  add_sSup_distrib := boundProfile_add_sSup_distrib
  sSup_add_distrib S B := by
    rw [add_comm, boundProfile_add_sSup_distrib]
    congr 1
    ext A
    rw [add_comm]

end Erdos289
