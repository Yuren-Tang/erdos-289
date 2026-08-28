import Universal.PhysicalPartialMonoid

import Mathlib.Algebra.Category.MonCat.Basic

/-!
# Coherent graded observations

This module translates the observation system fixed in the specification: an
`AddCommMonCat`-valued functor `Q`, a natural transformation from the constant
observation monoid, its grading by a second commutative monoid, and the
resulting additive physical observations.
-/

open CategoryTheory
open scoped BigOperators

namespace Erdos289

universe u v w x

/-- A coherent observation system `Q : I ⥤ CMon` together with
`ρ : ΔΓ ⟶ Q`.  We use Mathlib's additive presentation `AddCommMonCat`, in
accordance with the additive formulas in the sealed specification. -/
structure ObservationSystem (I : Type u) [Category.{v} I]
    (Γ : Type w) [AddCommMonoid Γ] where
  /-- The functorial observation monoid. -/
  Q : I ⥤ AddCommMonCat.{w}
  /-- The coherent map from the constant base observation. -/
  rho : (Functor.const I).obj (AddCommMonCat.of Γ) ⟶ Q

namespace ObservationSystem

variable {I : Type u} [Category.{v} I]
variable {Γ : Type w} [AddCommMonoid Γ]

/-- The graded observation functor `Q̃(i) = U(Q(i)) × M`. -/
def gradedObservation (O : ObservationSystem I Γ)
    (M : Type x) [AddCommMonoid M] : I ⥤ AddCommMonCat.{max w x} where
  obj i := AddCommMonCat.of (O.Q.obj i × M)
  map f := AddCommMonCat.ofHom
    { toFun := fun p ↦ (O.Q.map f p.1, p.2)
      map_zero' := by simp
      map_add' := by simp }
  map_id i := by
    ext p <;> simp
  map_comp f g := by
    ext p <;> simp

@[simp]
theorem gradedObservation_map_apply (O : ObservationSystem I Γ)
    (M : Type x) [AddCommMonoid M] {i j : I} (f : i ⟶ j)
    (p : O.Q.obj i × M) :
    (O.gradedObservation M).map f p = (O.Q.map f p.1, p.2) :=
  rfl

/-- A map out of the physical partial monoid which is additive on every direct
finite multiplication domain. -/
structure PhysicalAdditiveMap (G : Graphᵣ.{u}) (Θ : Set ℕ+)
    (A : Type w) [AddCommMonoid A] where
  /-- Underlying observation map. -/
  toFun : FiniteComponentState G Θ → A
  /-- The empty physical state maps to zero. -/
  map_empty : toFun (emptyPhysicalState G Θ) = 0
  /-- Additivity on the canonical direct finite multiplication domain. -/
  map_finitePhysicalUnion : ∀ {J : Type u} [Fintype J]
      (S : NaryPhysicalDomain G Θ J),
      toFun (finitePhysicalUnion S) = ∑ j, toFun (S.1 j)

instance (G : Graphᵣ.{u}) (Θ : Set ℕ+) (A : Type w) [AddCommMonoid A] :
    CoeFun (PhysicalAdditiveMap G Θ A)
      (fun _ ↦ FiniteComponentState G Θ → A) :=
  ⟨PhysicalAdditiveMap.toFun⟩

@[simp]
theorem PhysicalAdditiveMap.map_empty_apply
    {G : Graphᵣ.{u}} {Θ : Set ℕ+} {A : Type w} [AddCommMonoid A]
    (f : PhysicalAdditiveMap G Θ A) :
    f (emptyPhysicalState G Θ) = 0 :=
  f.map_empty

/-- The physical observation `ω_i = (ρ_i W, g)`. -/
def physicalObservation (O : ObservationSystem I Γ)
    (M : Type x) [AddCommMonoid M]
    {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    (W : PhysicalAdditiveMap G Θ Γ)
    (g : PhysicalAdditiveMap G Θ M) (i : I) :
    FiniteComponentState G Θ → O.Q.obj i × M :=
  fun c ↦ (O.rho.app i (W c), g c)

@[simp]
theorem physicalObservation_fst (O : ObservationSystem I Γ)
    (M : Type x) [AddCommMonoid M]
    {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    (W : PhysicalAdditiveMap G Θ Γ)
    (g : PhysicalAdditiveMap G Θ M) (i : I)
    (c : FiniteComponentState G Θ) :
    (O.physicalObservation M W g i c).1 = O.rho.app i (W c) :=
  rfl

@[simp]
theorem physicalObservation_snd (O : ObservationSystem I Γ)
    (M : Type x) [AddCommMonoid M]
    {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    (W : PhysicalAdditiveMap G Θ Γ)
    (g : PhysicalAdditiveMap G Θ M) (i : I)
    (c : FiniteComponentState G Θ) :
    (O.physicalObservation M W g i c).2 = g c :=
  rfl

/-- Naturality of the physical observations. -/
theorem physicalObservation_naturality (O : ObservationSystem I Γ)
    (M : Type x) [AddCommMonoid M]
    {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    (W : PhysicalAdditiveMap G Θ Γ)
    (g : PhysicalAdditiveMap G Θ M) {i j : I} (f : i ⟶ j)
    (c : FiniteComponentState G Θ) :
    (O.gradedObservation M).map f (O.physicalObservation M W g i c) =
      O.physicalObservation M W g j c := by
  apply Prod.ext
  · have h := ConcreteCategory.congr_hom (O.rho.naturality f)
    simpa using (h (W c)).symm
  · rfl

/-- Every physical observation is additive on the direct finite physical
multiplication domain. -/
theorem physicalObservation_finitePhysicalUnion
    (O : ObservationSystem I Γ) (M : Type x) [AddCommMonoid M]
    {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    (W : PhysicalAdditiveMap G Θ Γ)
    (g : PhysicalAdditiveMap G Θ M) (i : I)
    {J : Type u} [Fintype J] (S : NaryPhysicalDomain G Θ J) :
    O.physicalObservation M W g i (finitePhysicalUnion S) =
      ∑ j, O.physicalObservation M W g i (S.1 j) := by
  apply Prod.ext
  · rw [Prod.fst_sum]
    simp only [physicalObservation_fst]
    rw [W.map_finitePhysicalUnion]
    exact map_sum (O.rho.app i).hom (fun j ↦ W (S.1 j)) Finset.univ
  · rw [Prod.snd_sum]
    simp only [physicalObservation_snd]
    exact g.map_finitePhysicalUnion S

end ObservationSystem

end Erdos289
