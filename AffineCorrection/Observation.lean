module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.Const

@[expose] public section

/-!
# Coherent abelian observation systems

The universal observation datum is a functor `Q : I ⥤ Ab` together with a
natural transformation `Δ Γ ⟶ Q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace AffineCorrection

universe u v w

/-- A coherent additive observation system on exact values `Γ`. -/
structure ObservationSystem
    (I : Type u) [Category.{w, u} I]
    (Γ : Type v) [AddCommGroup Γ] where
  /-- Observation group at each level. -/
  Q : I ⥤ AddCommGrpCat.{v}
  /-- Natural observation of exact values at every level. -/
  ρ : (Functor.const I).obj (AddCommGrpCat.of Γ) ⟶ Q

namespace ObservationSystem

variable
    {I : Type u} [Category.{w, u} I]
    {Γ : Type v} [AddCommGroup Γ]
    (O : ObservationSystem I Γ)

/-- Observation homomorphism at level `i`. -/
def observe (i : I) : Γ →+ O.Q.obj i :=
  ConcreteCategory.hom (O.ρ.app i)

/-- Transition homomorphism attached to an observation morphism. -/
def transition {i j : I} (f : i ⟶ j) :
    O.Q.obj i →+ O.Q.obj j :=
  ConcreteCategory.hom (O.Q.map f)

@[simp]
theorem transition_id (i : I) (a : O.Q.obj i) :
    O.transition (𝟙 i) a = a := by
  simp [transition]

@[simp]
theorem transition_comp
    {i j k : I} (f : i ⟶ j) (g : j ⟶ k)
    (a : O.Q.obj i) :
    O.transition (f ≫ g) a =
      O.transition g (O.transition f a) := by
  simp [transition]

/-- Elementwise naturality of the exact-value observation cone. -/
@[simp]
theorem transition_observe
    {i j : I} (f : i ⟶ j) (x : Γ) :
    O.transition f (O.observe i x) = O.observe j x := by
  simpa [transition, observe] using (O.ρ.naturality_apply f x).symm

end ObservationSystem

end AffineCorrection
