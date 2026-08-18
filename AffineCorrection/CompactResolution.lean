module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection.Observation
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-!
# Compact quotient resolution

For an additive commutative group `A`, the observation stages are its finitely
generated subgroups, i.e. the compact elements of the subgroup lattice.  A
stage `H` observes `A` through the canonical quotient `A ⧸ H`; inclusions of
stages induce the unique quotient transition maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace AffineCorrection

universe u

/-- A compact observation stage: a finitely generated additive subgroup. -/
abbrev CompactStage (A : Type u) [AddCommGroup A] :=
  {H : AddSubgroup A // H.FG}

namespace CompactStage

variable {A : Type u} [AddCommGroup A]

/-- The least compact stage. -/
def bot : CompactStage A :=
  ⟨⊥, AddSubgroup.FG.bot⟩

/-- The finite join of two compact stages. -/
def sup (H K : CompactStage A) : CompactStage A :=
  ⟨H.1 ⊔ K.1, H.2.sup K.2⟩

@[simp]
theorem coe_bot : (bot : CompactStage A).1 = ⊥ :=
  rfl

@[simp]
theorem coe_sup (H K : CompactStage A) : (sup H K).1 = H.1 ⊔ K.1 :=
  rfl

theorem le_sup_left (H K : CompactStage A) : H ≤ sup H K :=
  show H.1 ≤ H.1 ⊔ K.1 from _root_.le_sup_left

theorem le_sup_right (H K : CompactStage A) : K ≤ sup H K :=
  show K.1 ≤ H.1 ⊔ K.1 from _root_.le_sup_right

/-- Compact stages are directed by finite join. -/
theorem directed : Directed (· ≤ ·) (fun H : CompactStage A => H) := by
  intro H K
  exact ⟨sup H K, le_sup_left H K, le_sup_right H K⟩

end CompactStage

namespace CompactResolution

variable (A : Type u) [AddCommGroup A]

/-- Canonical quotient transition attached to an inclusion of stages. -/
def transition {H K : CompactStage A} (h : H ≤ K) :
    (A ⧸ H.1) →+ (A ⧸ K.1) :=
  QuotientAddGroup.map H.1 K.1 (AddMonoidHom.id A) <| by
    intro x hx
    exact h hx

@[simp]
theorem transition_mk {H K : CompactStage A} (h : H ≤ K) (x : A) :
    transition A h (QuotientAddGroup.mk' H.1 x) =
      QuotientAddGroup.mk' K.1 x := by
  exact QuotientAddGroup.map_mk' _ _ _ _ x

@[simp]
theorem transition_id (H : CompactStage A) :
    transition A (le_refl H) = AddMonoidHom.id (A ⧸ H.1) := by
  apply QuotientAddGroup.addMonoidHom_ext H.1
  ext x
  change transition A (le_refl H) (QuotientAddGroup.mk' H.1 x) =
    QuotientAddGroup.mk' H.1 x
  exact transition_mk A (le_refl H) x

@[simp]
theorem transition_comp
    {H K L : CompactStage A} (hHK : H ≤ K) (hKL : K ≤ L) :
    (transition A hKL).comp (transition A hHK) =
      transition A (hHK.trans hKL) := by
  apply QuotientAddGroup.addMonoidHom_ext H.1
  ext x
  change
    transition A hKL
        (transition A hHK (QuotientAddGroup.mk' H.1 x)) =
      transition A (hHK.trans hKL) (QuotientAddGroup.mk' H.1 x)
  rw [transition_mk, transition_mk, transition_mk]

/-- The quotient observation functor on compact stages. -/
def functor : CompactStage A ⥤ AddCommGrpCat.{u} where
  obj H := AddCommGrpCat.of (A ⧸ H.1)
  map {H K} f := AddCommGrpCat.ofHom (transition A (leOfHom f))
  map_id H := by
    ext x
    exact congrArg
      (fun q : (A ⧸ H.1) →+ (A ⧸ H.1) => q x)
      (transition_id A H)
  map_comp f g := by
    ext x
    exact congrArg
      (fun q : (A ⧸ _) →+ (A ⧸ _) => q x)
      (transition_comp A (leOfHom f) (leOfHom g)).symm

/-- Exact values observed at every compact quotient stage. -/
def system : ObservationSystem (CompactStage A) A where
  Q := functor A
  ρ :=
    { app := fun H => AddCommGrpCat.ofHom (QuotientAddGroup.mk' H.1)
      naturality := by
        intro H K f
        ext x
        exact (transition_mk A (leOfHom f) x).symm }

@[simp]
theorem system_observe (H : CompactStage A) (x : A) :
    (system A).observe H x = QuotientAddGroup.mk' H.1 x :=
  rfl

end CompactResolution

end AffineCorrection
