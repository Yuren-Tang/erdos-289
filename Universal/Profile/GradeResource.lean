import Universal.PhysicalPartialMonoid

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Quantale

/-!
# Grade-resource labels and the free powerset quantale

The tensor is literal Minkowski addition of subsets.  The universal theorem
is stated by its generator, arbitrary-join, and tensor characterizations.
-/

open scoped Pointwise

namespace Erdos289

universe u v w

/-- A label records an exact grade and a resource upper bound. -/
abbrev GradeResourceLabel (M : Type u) (U : Type v) := M × U

/-- The powerset of an additive label monoid. -/
abbrev PowersetQuantale (R : Type u) := Set R

instance {R : Type u} : CompleteLattice (PowersetQuantale R) :=
  inferInstanceAs (CompleteLattice (Set R))

instance {R : Type u} [AddCommMonoid R] : AddCommMonoid (PowersetQuantale R) :=
  Set.addCommMonoid

/-- Minkowski addition distributes over arbitrary unions on both sides. -/
instance {R : Type u} [AddCommMonoid R] : IsAddQuantale (PowersetQuantale R) where
  add_sSup_distrib A S := by
    change A + ⋃₀ S = ⋃ B ∈ S, A + B
    exact Set.image2_sUnion_right (· + ·) A S
  sSup_add_distrib S B := by
    change (⋃₀ S) + B = ⋃ A ∈ S, A + B
    exact Set.image2_sUnion_left (· + ·) S B

/-- The canonical generator of the powerset quantale. -/
def powersetQuantaleGenerator {R : Type u} [AddCommMonoid R] :
    R →+ PowersetQuantale R :=
  Set.singletonAddMonoidHom

/-- Extension of a monoid map by arbitrary join. -/
noncomputable def powersetQuantaleLift {R : Type u} {Q : Type v}
    [AddCommMonoid R] [AddCommMonoid Q] [CompleteLattice Q] [IsAddQuantale Q]
    (f : R →+ Q) (A : PowersetQuantale R) : Q :=
  ⨆ r : A, f r.1

@[simp]
theorem powersetQuantaleLift_singleton {R : Type u} {Q : Type v}
    [AddCommMonoid R] [AddCommMonoid Q] [CompleteLattice Q] [IsAddQuantale Q]
    (f : R →+ Q) (r : R) : powersetQuantaleLift f {r} = f r := by
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    rw [x.2]
  · exact le_iSup_of_le (⟨r, rfl⟩ : ({r} : Set R)) le_rfl

/-- The extension preserves arbitrary joins. -/
theorem powersetQuantaleLift_sUnion {R : Type u} {Q : Type v}
    [AddCommMonoid R] [AddCommMonoid Q] [CompleteLattice Q] [IsAddQuantale Q]
    (f : R →+ Q) (S : Set (PowersetQuantale R)) :
    powersetQuantaleLift f (⋃₀ S) = ⨆ A ∈ S, powersetQuantaleLift f A := by
  apply le_antisymm
  · refine iSup_le fun r ↦ ?_
    obtain ⟨A, hAS, hrA⟩ := r.2
    exact le_iSup_of_le A (le_iSup_of_le hAS
      (le_iSup_of_le (⟨r.1, hrA⟩ : A) le_rfl))
  · refine iSup_le fun A ↦ iSup_le fun hAS ↦ ?_
    refine iSup_le fun r ↦ ?_
    exact le_iSup_of_le
      (⟨r.1, ⟨A, hAS, r.2⟩⟩ : (⋃₀ S : Set R)) le_rfl

/-- The extension preserves the Minkowski tensor. -/
theorem powersetQuantaleLift_add {R : Type u} {Q : Type v}
    [AddCommMonoid R] [AddCommMonoid Q] [CompleteLattice Q] [IsAddQuantale Q]
    (f : R →+ Q) (A B : PowersetQuantale R) :
    powersetQuantaleLift f (A + B) =
      powersetQuantaleLift f A + powersetQuantaleLift f B := by
  apply le_antisymm
  · refine iSup_le fun r ↦ ?_
    rcases r.2 with ⟨a, ha, b, hb, hab⟩
    rw [← hab]
    rw [map_add]
    exact add_le_add
      (le_iSup_of_le (⟨a, ha⟩ : A) le_rfl)
      (le_iSup_of_le (⟨b, hb⟩ : B) le_rfl)
  · change (⨆ a : A, f a.1) + (⨆ b : B, f b.1) ≤
      ⨆ r : (A + B), f r.1
    rw [AddQuantale.iSup_add_distrib]
    refine iSup_le fun a ↦ ?_
    rw [AddQuantale.add_iSup_distrib]
    refine iSup_le fun b ↦ ?_
    rw [← map_add]
    exact le_iSup_of_le
      (⟨a.1 + b.1, ⟨a.1, a.2, b.1, b.2, rfl⟩⟩ : A + B) le_rfl

/-- Universal property of the free complete idempotent commutative quantale
on an additive commutative monoid. -/
theorem powersetQuantale_free {R : Type u} {Q : Type v}
    [AddCommMonoid R] [AddCommMonoid Q] [CompleteLattice Q] [IsAddQuantale Q]
    (f : R →+ Q) :
    ∃! F : PowersetQuantale R → Q,
      (∀ r, F {r} = f r) ∧
      (∀ S : Set (PowersetQuantale R), F (⋃₀ S) = ⨆ A ∈ S, F A) ∧
      (∀ A B, F (A + B) = F A + F B) := by
  refine ⟨powersetQuantaleLift f,
    ⟨powersetQuantaleLift_singleton f,
      powersetQuantaleLift_sUnion f, powersetQuantaleLift_add f⟩, ?_⟩
  intro F hF
  funext A
  let S : Set (PowersetQuantale R) := Set.range fun r : A ↦ ({r.1} : Set R)
  have hA : A = ⋃₀ S := by
    ext r
    simp [S]
  calc
    F A = F (⋃₀ S) := congrArg F hA
    _ = ⨆ B ∈ S, F B := hF.2.1 S
    _ = powersetQuantaleLift f A := by
      apply le_antisymm
      · refine iSup_le fun B ↦ iSup_le fun hBS ↦ ?_
        obtain ⟨r, rfl⟩ := hBS
        rw [hF.1 r.1]
        exact le_iSup_of_le (r : A) le_rfl
      · refine iSup_le fun r ↦ ?_
        exact le_iSup_of_le ({r.1} : Set R)
          (le_iSup_of_le ⟨r, rfl⟩ (hF.1 r.1).ge)

end Erdos289
