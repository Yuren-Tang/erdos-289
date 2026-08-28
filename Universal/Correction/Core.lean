import Universal.Correction.Observation

/-!
# The graded correction category

Corrections and their operations are the literal Grothendieck construction
specified by `(u; a)` with composition
`(v; b) ∘ (u; a) = (v ∘ u; Q̃(v)(a) + b)`.
-/

open CategoryTheory

namespace Erdos289

universe u v w x

namespace ObservationSystem

variable {I : Type u} [Category.{v} I]
variable {Γ : Type w} [AddCommMonoid Γ]
variable (O : ObservationSystem I Γ)
variable (M : Type x) [AddCommMonoid M]

/-- A correction `(u; a) : i ⟶ j` in the fixed Grothendieck correction
category. -/
structure Correction (i j : I) where
  /-- The base arrow `u : i ⟶ j`. -/
  base : i ⟶ j
  /-- The correction label `a ∈ Q̃(j)`. -/
  label : (O.gradedObservation M).obj j

namespace Correction

variable {O M}
variable {i j k l : I}

@[ext]
theorem ext {φ ψ : O.Correction M i j}
    (hbase : φ.base = ψ.base) (hlabel : φ.label = ψ.label) : φ = ψ := by
  cases φ
  cases ψ
  simp_all

/-- Identity correction `(𝟙 i; 0)`. -/
noncomputable def id (i : I) : O.Correction M i i where
  base := 𝟙 i
  label := 0

/-- Fixed Grothendieck composition
`(v; b) ∘ (u; a) = (v ∘ u; Q̃(v)(a) + b)`. -/
noncomputable def comp (φ : O.Correction M i j)
    (ψ : O.Correction M j k) : O.Correction M i k where
  base := φ.base ≫ ψ.base
  label := (O.gradedObservation M).map ψ.base φ.label + ψ.label

@[simp]
theorem id_base (i : I) :
    (Correction.id (O := O) (M := M) i).base = 𝟙 i :=
  rfl

@[simp]
theorem id_label (i : I) :
    (Correction.id (O := O) (M := M) i).label = 0 :=
  rfl

@[simp]
theorem comp_base (φ : O.Correction M i j) (ψ : O.Correction M j k) :
    (φ.comp ψ).base = φ.base ≫ ψ.base :=
  rfl

/-- The exact label formula fixed by the Grothendieck construction. -/
@[simp]
theorem comp_label (φ : O.Correction M i j) (ψ : O.Correction M j k) :
    (φ.comp ψ).label =
      (O.gradedObservation M).map ψ.base φ.label + ψ.label :=
  rfl

@[simp]
theorem id_comp (φ : O.Correction M i j) :
    (Correction.id (O := O) (M := M) i).comp φ = φ := by
  apply Correction.ext
  · simp [comp, id]
  · simp [comp, id]

@[simp]
theorem comp_id (φ : O.Correction M i j) :
    φ.comp (Correction.id (O := O) (M := M) j) = φ := by
  apply Correction.ext
  · simp [comp, id]
  · simp [comp, id]

@[simp]
theorem comp_assoc (φ : O.Correction M i j) (ψ : O.Correction M j k)
    (χ : O.Correction M k l) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  apply Correction.ext
  · simp [comp, Category.assoc]
  · simp [comp, add_assoc]

end Correction

/-- The required source fibre
`T(φ) = {x ∈ Q̃(i) | Q̃(φ.base)(x) = φ.label}`. -/
def Required {i j : I} (φ : O.Correction M i j) :=
  {x : (O.gradedObservation M).obj i //
    (O.gradedObservation M).map φ.base x = φ.label}

namespace Required

variable {O M}
variable {i j : I} {φ : O.Correction M i j}

@[simp]
theorem condition (x : O.Required M φ) :
    (O.gradedObservation M).map φ.base x.1 = φ.label :=
  x.2

/-- The projection of the required fibre to its source observation. -/
def sourceValue (x : O.Required M φ) : (O.gradedObservation M).obj i :=
  x.1

@[simp]
theorem sourceValue_apply (x : O.Required M φ) : sourceValue x = x.1 :=
  rfl

end Required

end ObservationSystem

end Erdos289
