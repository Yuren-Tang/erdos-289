import AffineCorrection.Observation

/-!
# Graded correction category

This is the strict one-object-fibre normal form of the Grothendieck
construction

`∫_I B (UQ × M)`.

A morphism carries its base observation arrow, correction label, and grade in
one object.  Grade is not an external homogeneity condition.
-/

set_option autoImplicit false

open CategoryTheory

namespace AffineCorrection

universe u v w y

variable
    {I : Type u} [Category.{w, u} I]
    {Γ : Type v} [AddCommGroup Γ]
    {M : Type y} [AddCommMonoid M]

/-- Objects of the graded correction category are observation levels. -/
structure GradedCorrection (O : ObservationSystem I Γ) (M : Type y) where
  /-- Underlying observation level. -/
  level : I

namespace GradedCorrection

variable (O : ObservationSystem I Γ) (M : Type y) [AddCommMonoid M]

/--
A graded correction morphism consists of a base arrow, destination correction
label, and grade.
-/
@[ext]
structure Hom (X Y : GradedCorrection O M) where
  /-- Base observation morphism. -/
  base : X.level ⟶ Y.level
  /-- Affine correction label in the destination observation group. -/
  label : O.Q.obj Y.level
  /-- Grade consumed by this correction. -/
  grade : M

namespace Hom

variable {O M}
variable {W X Y Z : GradedCorrection O M}

/-- Identity graded correction. -/
def id (X : GradedCorrection O M) : Hom O M X X :=
  ⟨𝟙 X.level, 0, 0⟩

/-- Grothendieck composition of correction and grade labels. -/
def comp (f : Hom O M W X) (g : Hom O M X Y) : Hom O M W Y :=
  ⟨f.base ≫ g.base,
    O.transition g.base f.label + g.label,
    f.grade + g.grade⟩

end Hom

instance : Category (GradedCorrection O M) where
  Hom := Hom O M
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    ext
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
  comp_id := by
    intro X Y f
    ext
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
    · simp [Hom.comp, Hom.id]
  assoc := by
    intro W X Y Z f g h
    ext
    · simp [Hom.comp, Category.assoc]
    · simp [Hom.comp, add_assoc]
    · simp [Hom.comp, add_assoc]

@[simp]
theorem comp_base
    {W X Y : GradedCorrection O M} (f : W ⟶ X) (g : X ⟶ Y) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_label
    {W X Y : GradedCorrection O M} (f : W ⟶ X) (g : X ⟶ Y) :
    (f ≫ g).label = O.transition g.base f.label + g.label :=
  rfl

@[simp]
theorem comp_grade
    {W X Y : GradedCorrection O M} (f : W ⟶ X) (g : X ⟶ Y) :
    (f ≫ g).grade = f.grade + g.grade :=
  rfl

/--
The required source type of a graded correction.

This subtype is the Set-level pullback of
`Q(u) × id_M : Q(i) × M → Q(j) × M` along the point `(d,m)`.
-/
def Required {X Y : GradedCorrection O M} (f : X ⟶ Y) :=
  {a : O.Q.obj X.level × M //
    O.transition f.base a.1 = f.label ∧ a.2 = f.grade}

/-- Target graded correction over a chosen base arrow and grade. -/
def target
    (τ : Γ) {X Y : GradedCorrection O M}
    (u : X.level ⟶ Y.level) (m : M) : X ⟶ Y :=
  ⟨u, O.observe Y.level τ, m⟩

/--
The distinguished target point in the required source pullback.
-/
def targetPoint
    (τ : Γ) {X Y : GradedCorrection O M}
    (u : X.level ⟶ Y.level) (m : M) :
    Required O M (target O M τ u m) :=
  ⟨(O.observe X.level τ, m), by
    constructor
    · exact O.transition_observe u τ
    · rfl⟩

end GradedCorrection

end AffineCorrection
