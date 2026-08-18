module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Algebra.Order.Quantale
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Set.Lattice

@[expose] public section

/-!
# The grade-resource quantale

For additive commutative monoids `M` and `B`, the powerset of `M × B` is the
free join-completion of the resource monoid.  Multiplication is Minkowski sum;
arbitrary joins are unions.  This is the intrinsic value object used by the
enriched saturation engine.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AffineCorrection

universe u v

/-- Profiles of simultaneously attainable grades and resource bounds. -/
abbrev GradeResource (M : Type u) (B : Type v) := Set (M × B)

namespace GradeResource

variable {M : Type u} {B : Type v}

variable [AddCommMonoid M] [AddCommMonoid B]

/-- Minkowski composition of grade-resource profiles. -/
protected def mul (P Q : GradeResource M B) : GradeResource M B :=
  {x | ∃ p ∈ P, ∃ q ∈ Q, x = p + q}

/-- The profile containing only the zero grade and zero resource. -/
protected def one : GradeResource M B := {(0, 0)}

instance : Mul (GradeResource M B) := ⟨GradeResource.mul⟩
instance : One (GradeResource M B) := ⟨GradeResource.one⟩

theorem mem_mul {x : M × B} {P Q : GradeResource M B} :
    x ∈ P * Q ↔ ∃ p ∈ P, ∃ q ∈ Q, x = p + q :=
  Iff.rfl

@[simp]
theorem mem_one {x : M × B} : x ∈ (1 : GradeResource M B) ↔ x = 0 := by
  change x ∈ ({(0, 0)} : Set (M × B)) ↔ x = 0
  simp only [Set.mem_singleton_iff]
  rfl

instance : CommMonoid (GradeResource M B) where
  mul_assoc P Q R := by
    ext x
    constructor
    · rintro ⟨pq, ⟨p, hp, q, hq, rfl⟩, r, hr, rfl⟩
      exact ⟨p, hp, q + r, ⟨q, hq, r, hr, rfl⟩, by simp [add_assoc]⟩
    · rintro ⟨p, hp, qr, ⟨q, hq, r, hr, rfl⟩, rfl⟩
      exact ⟨p + q, ⟨p, hp, q, hq, rfl⟩, r, hr, by simp [add_assoc]⟩
  one_mul P := by
    ext x
    constructor
    · rintro ⟨z, hz, p, hp, rfl⟩
      have hz0 : z = 0 := mem_one.mp hz
      subst z
      have hzero : ((0, 0) : M × B) + p = p := by
        rcases p with ⟨m, b⟩
        simp
      rwa [hzero]
    · intro hx
      exact ⟨0, by simp, x, hx, by simp⟩
  mul_one P := by
    ext x
    constructor
    · rintro ⟨p, hp, z, hz, rfl⟩
      have hz0 : z = 0 := mem_one.mp hz
      subst z
      have hzero : p + ((0, 0) : M × B) = p := by
        rcases p with ⟨m, b⟩
        simp
      rwa [hzero]
    · intro hx
      exact ⟨x, hx, 0, by simp, by simp⟩
  mul_comm P Q := by
    ext x
    constructor
    · rintro ⟨p, hp, q, hq, rfl⟩
      exact ⟨q, hq, p, hp, add_comm p q⟩
    · rintro ⟨q, hq, p, hp, rfl⟩
      exact ⟨p, hp, q, hq, add_comm q p⟩

/-- Minkowski composition distributes over arbitrary unions on both sides. -/
instance : IsQuantale (GradeResource M B) where
  mul_sSup_distrib P S := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨p, hp, q, hq, rfl⟩
      change q ∈ sSup S at hq
      rcases hq with ⟨Q, hQS, hqQ⟩
      have hle : P * Q ≤ ⨆ Y ∈ S, P * Y :=
        le_trans (le_iSup (fun _ : Q ∈ S => P * Q) hQS)
          (le_iSup (fun Y => ⨆ _ : Y ∈ S, P * Y) Q)
      exact hle ⟨p, hp, q, hqQ, rfl⟩
    · refine iSup_le fun Q => iSup_le fun hQS => ?_
      intro x hx
      rcases hx with ⟨p, hp, q, hqQ, rfl⟩
      exact ⟨p, hp, q, ⟨Q, hQS, hqQ⟩, rfl⟩
  sSup_mul_distrib S Q := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨p, hp, q, hq, rfl⟩
      change p ∈ sSup S at hp
      rcases hp with ⟨P, hPS, hpP⟩
      have hle : P * Q ≤ ⨆ Y ∈ S, Y * Q :=
        le_trans (le_iSup (fun _ : P ∈ S => P * Q) hPS)
          (le_iSup (fun Y => ⨆ _ : Y ∈ S, Y * Q) P)
      exact hle ⟨p, hpP, q, hq, rfl⟩
    · refine iSup_le fun P => iSup_le fun hPS => ?_
      intro x hx
      rcases hx with ⟨p, hpP, q, hq, rfl⟩
      exact ⟨p, ⟨P, hPS, hpP⟩, q, hq, rfl⟩

end GradeResource

end AffineCorrection
