import Universal.Correction.Core
import Universal.PhysicalPartialMonoid

import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Types.Basic

/-!
# Required fibres and physical realizers

All objects in this module are literal pullbacks in `Type`.  In particular,
`Covers` is regular epimorphicity of the family-realizer projection, expressed
by its Mathlib characterization as surjectivity in `Type`.
-/

open CategoryTheory

namespace Erdos289

universe u v w x y z

/-- The canonical universe-lifted presentation of a function as a morphism in
the fixed category `Type`. -/
def typeLiftMap {A : Type u} {B : Type v} (f : A → B) :
    ULift.{v} A → ULift.{u} B :=
  fun a ↦ ULift.up (f a.down)

/-- Invariant regular-epimorphism predicate for a map of possibly differently
sized Lean types. -/
abbrev TypeRegularEpi {A : Type u} {B : Type v} (f : A → B) : Prop :=
  IsRegularEpi (TypeCat.ofHom (typeLiftMap f))

/-- In the fixed category of types, concrete surjectivity is exactly
categorical regular epimorphicity (after the canonical universe lift). -/
theorem type_regularEpi_iff_surjective {A : Type u} {B : Type v} (f : A → B) :
    TypeRegularEpi f ↔ Function.Surjective f := by
  constructor
  · intro h
    have hs : Function.Surjective (typeLiftMap f) :=
      (ofHom_epi_iff_surjective (typeLiftMap f)).1
        (RegularEpi.epi _ h.regularEpi.some)
    intro b
    obtain ⟨a, ha⟩ := hs (ULift.up b)
    exact ⟨a.down, congrArg ULift.down ha⟩
  · intro h
    have hs : Function.Surjective (typeLiftMap f) := by
      rintro ⟨b⟩
      obtain ⟨a, ha⟩ := h b
      exact ⟨ULift.up a, congrArg ULift.up ha⟩
    letI : Epi (TypeCat.ofHom (typeLiftMap f)) :=
      (ofHom_epi_iff_surjective (typeLiftMap f)).2 hs
    exact IsRegularEpiCategory.regularEpiOfEpi _

/-- The literal pullback of two maps in `Type`. -/
structure TypePullback {A : Type u} {B : Type v} {Z : Type w}
    (f : A → Z) (g : B → Z) where
  left : A
  right : B
  condition : f left = g right

namespace TypePullback

variable {A : Type u} {B : Type v} {Z : Type w}
variable {f : A → Z} {g : B → Z}

@[ext]
theorem ext {p q : TypePullback f g}
    (hleft : p.left = q.left) (hright : p.right = q.right) : p = q := by
  cases p
  cases q
  simp_all

/-- Projection of a pullback to its left factor. -/
def fst (p : TypePullback f g) : A := p.left

/-- Projection of a pullback to its right factor. -/
def snd (p : TypePullback f g) : B := p.right

/-- Regular epimorphisms in `Type` are stable under pullback: the left
projection is surjective when the map on the right is surjective. -/
theorem fst_surjective_of_right_surjective (hg : Function.Surjective g) :
    Function.Surjective (fst : TypePullback f g → A) := by
  intro a
  obtain ⟨b, hb⟩ := hg (f a)
  exact ⟨⟨a, b, hb.symm⟩, rfl⟩

end TypePullback

namespace ObservationSystem

variable {I : Type u} [Category.{v} I]
variable {Γ : Type w} [AddCommMonoid Γ]
variable (O : ObservationSystem I Γ)
variable (M : Type x) [AddCommMonoid M]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : PhysicalAdditiveMap G Θ Γ)
variable (g : PhysicalAdditiveMap G Θ M)

/-- The universal realizer
`C ×_{Q̃(i)} Required(φ)`. -/
def UniversalRealizer {i j : I} (φ : O.Correction M i j) :=
  TypePullback (O.physicalObservation M W g i)
    (Required.sourceValue : O.Required M φ → (O.gradedObservation M).obj i)

namespace UniversalRealizer

variable {O M W g}
variable {i j : I} {φ : O.Correction M i j}

/-- Universal-realizer projection to the physical state object. -/
def state (r : O.UniversalRealizer M W g φ) : FiniteComponentState G Θ :=
  r.left

/-- Universal-realizer projection to the required fibre. -/
def required (r : O.UniversalRealizer M W g φ) : O.Required M φ :=
  r.right

@[simp]
theorem observation_eq (r : O.UniversalRealizer M W g φ) :
    O.physicalObservation M W g i r.state = r.required.1 :=
  r.condition

end UniversalRealizer

/-- The family realizer `F ×_C UniversalRealizer(φ)`. -/
def FamilyRealizer {i j : I}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (φ : O.Correction M i j) :=
  TypePullback F.hom
    (UniversalRealizer.state : O.UniversalRealizer M W g φ →
      FiniteComponentState G Θ)

namespace FamilyRealizer

variable {O M W g}
variable {i j : I} {φ : O.Correction M i j}
variable {F : PhysicalFamily (FiniteComponentState G Θ)}

/-- Projection to the branch of the physical family. -/
def branch (r : O.FamilyRealizer M W g F φ) : F.left :=
  r.left

/-- Projection to the universal realizer. -/
def universal (r : O.FamilyRealizer M W g F φ) :
    O.UniversalRealizer M W g φ :=
  r.right

/-- Projection of a family realizer to the required fibre. -/
def required (r : O.FamilyRealizer M W g F φ) : O.Required M φ :=
  r.universal.required

@[simp]
theorem family_state_eq (r : O.FamilyRealizer M W g F φ) :
    F.hom r.branch = r.universal.state :=
  r.condition

end FamilyRealizer

/-- The direct base-change presentation
`F ×_{Q̃(i)} Required(φ)`. -/
def FamilyRequiredPullback {i j : I}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (φ : O.Correction M i j) :=
  TypePullback (fun branch ↦ O.physicalObservation M W g i (F.hom branch))
    (Required.sourceValue : O.Required M φ → (O.gradedObservation M).obj i)

/-- The canonical public base-change isomorphism
`FamilyRealizer(F,φ) ≃ F ×_{Q̃(i)} Required(φ)`. -/
def familyRealizerBaseChangeEquiv {i j : I}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (φ : O.Correction M i j) :
    O.FamilyRealizer M W g F φ ≃ O.FamilyRequiredPullback M W g F φ where
  toFun r :=
    { left := r.branch
      right := r.required
      condition := by
        rw [r.family_state_eq]
        exact r.universal.observation_eq }
  invFun r :=
    { left := r.left
      right :=
        { left := F.hom r.left
          right := r.right
          condition := r.condition }
      condition := rfl }
  left_inv r := by
    apply TypePullback.ext
    · rfl
    · apply TypePullback.ext
      · exact r.family_state_eq
      · rfl
  right_inv r := by
    apply TypePullback.ext <;> rfl

/-- The canonical map from the direct family-required pullback to the required
fibre. -/
def FamilyRequiredPullback.required {i j : I}
    {F : PhysicalFamily (FiniteComponentState G Θ)}
    {φ : O.Correction M i j}
    (r : O.FamilyRequiredPullback M W g F φ) : O.Required M φ :=
  r.right

/-- A physical family covers a correction exactly when the family-realizer
projection to the required fibre is a regular epimorphism; in `Type` this is
surjectivity. -/
def Covers {i j : I}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (φ : O.Correction M i j) : Prop :=
  Function.Surjective
    (FamilyRealizer.required : O.FamilyRealizer M W g F φ → O.Required M φ)

/-- Invariant formulation of `Covers` in the fixed category `Type`. -/
theorem covers_iff_regularEpi {i j : I}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (φ : O.Correction M i j) :
    O.Covers M W g F φ ↔
      TypeRegularEpi
        (FamilyRealizer.required :
          O.FamilyRealizer M W g F φ → O.Required M φ) := by
  exact (type_regularEpi_iff_surjective _).symm

/-- Covering can equivalently be checked on the direct base-change
presentation. -/
theorem covers_iff_familyRequiredPullback_surjective {i j : I}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (φ : O.Correction M i j) :
    O.Covers M W g F φ ↔ Function.Surjective
      (fun r : O.FamilyRequiredPullback M W g F φ ↦ r.right) := by
  constructor
  · intro h t
    obtain ⟨r, hr⟩ := h t
    exact ⟨O.familyRealizerBaseChangeEquiv M W g F φ r, hr⟩
  · intro h t
    obtain ⟨r, hr⟩ := h t
    exact ⟨(O.familyRealizerBaseChangeEquiv M W g F φ).symm r, hr⟩

end ObservationSystem

end Erdos289
