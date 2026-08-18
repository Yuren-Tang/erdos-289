module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection.Realizer

@[expose] public section

/-!
# Target literalization and exact-fibre spectrum transfer

The target-realizer type is the pullback of the realizer projection along the
distinguished target point.  Literalization says precisely that this pullback
maps into the exact physical fibre.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace AffineCorrection

universe u v w x y

variable
    {I : Type u} [Category.{w, u} I]
    {Γ : Type v} [AddCommGroup Γ]
    {M : Type y} [AddCommMonoid M]
    (O : ObservationSystem I Γ)

/-- Pullback of realizers along the distinguished target point. -/
def TargetRealizer
    {C : Type x} (W : C → Γ) (g : C → M)
    {X Y : GradedCorrection O M}
    (F : Set C) (u : X.level ⟶ Y.level) (τ : Γ) (m : M) :=
  {r : Realizer O W g F (GradedCorrection.target O M τ u m) //
    r.req = GradedCorrection.targetPoint O M τ u m}

/--
Literalization is factorization of every target realizer through the exact
physical fibre at `τ`, expressed elementwise in `Type`.
-/
def LiteralizesTarget
    {C : Type x} (W : C → Γ) (g : C → M)
    {X Y : GradedCorrection O M}
    (F : Set C) (u : X.level ⟶ Y.level) (τ : Γ) (m : M) : Prop :=
  ∀ r : TargetRealizer O W g F u τ m, W r.1.state.1 = τ

/--
Universal graded exact-fibre transfer.

No family homogeneity is present: the grade is already part of the target
correction fibre.
-/
theorem grade_mem_exactSpectrum_of_covers_target
    {C : Type x}
    (W : C → Γ) (g : C → M)
    {X Y : GradedCorrection O M}
    (F : Set C) (u : X.level ⟶ Y.level) (τ : Γ) (m : M)
    (hcov : Covers O W g F (GradedCorrection.target O M τ u m))
    (hlit : LiteralizesTarget O W g F u τ m) :
    m ∈ exactSpectrum W g τ := by
  let t := GradedCorrection.targetPoint O M τ u m
  rcases hcov t with ⟨r, hr⟩
  let tr : TargetRealizer O W g F u τ m := ⟨r, hr⟩
  refine ⟨r.state.1, hlit tr, ?_⟩
  exact r.grade_eq

end AffineCorrection
