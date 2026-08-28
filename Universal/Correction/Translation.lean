import Universal.Correction.Composition

import Mathlib.Algebra.Category.Grp.Basic

/-!
# Abelian translation certificate

The abelian specialization is recorded before forgetting to commutative
monoids.  Thus every subtraction below uses the same additive structure as the
original observation functor.
-/

open CategoryTheory
open scoped BigOperators

namespace Erdos289

universe u v w x

/-- An observation system whose observation functor genuinely takes values in
abelian groups. -/
structure AbelianObservationSystem (I : Type u) [Category.{v} I]
    (Γ : Type w) [AddCommGroup Γ] where
  /-- The abelian-group-valued observation functor. -/
  Q : I ⥤ AddCommGrpCat.{w}
  /-- The coherent base observation after forgetting only the inverse
structure. -/
  rho : (Functor.const I).obj (AddCommMonCat.of Γ) ⟶
    Q ⋙ forget₂ AddCommGrpCat AddCommMonCat

namespace AbelianObservationSystem

variable {I : Type u} [Category.{v} I]
variable {Γ : Type w} [AddCommGroup Γ]

/-- Forgetting inverses gives the observation system used by the correction
spine. -/
def toObservationSystem (A : AbelianObservationSystem I Γ) :
    ObservationSystem I Γ where
  Q := A.Q ⋙ forget₂ AddCommGrpCat AddCommMonCat
  rho := A.rho

end AbelianObservationSystem

namespace ObservationSystem

variable {I : Type u} [Category.{v} I]
variable {Γ : Type w} [AddCommGroup Γ]
variable (A : AbelianObservationSystem I Γ)
variable (M : Type x) [AddCommGroup M]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : PhysicalAdditiveMap G Θ Γ)
variable (g : PhysicalAdditiveMap G Θ M)
variable {i j k : I}

/-- Subtraction in the abelian graded observation, using the group structure
before it is forgotten to `AddCommMonCat`. -/
def abelianGradedSub (i : I)
    (p q : (A.toObservationSystem.gradedObservation M).obj i) :
    (A.toObservationSystem.gradedObservation M).obj i :=
  ((show A.Q.obj i from p.1) - (show A.Q.obj i from q.1), p.2 - q.2)

theorem gradedMap_abelianGradedSub {i j : I} (f : i ⟶ j)
    (p q : (A.toObservationSystem.gradedObservation M).obj i) :
    (A.toObservationSystem.gradedObservation M).map f
        (abelianGradedSub A M i p q) =
      abelianGradedSub A M j
        ((A.toObservationSystem.gradedObservation M).map f p)
        ((A.toObservationSystem.gradedObservation M).map f q) := by
  apply Prod.ext
  · change (A.Q.map f)
        ((show A.Q.obj i from p.1) - (show A.Q.obj i from q.1)) =
      (A.Q.map f) (show A.Q.obj i from p.1) -
        (A.Q.map f) (show A.Q.obj i from q.1)
    exact map_sub (A.Q.map f).hom
      (show A.Q.obj i from p.1) (show A.Q.obj i from q.1)
  · rfl

theorem abelianGradedSub_add_cancel (i : I)
    (p q : (A.toObservationSystem.gradedObservation M).obj i) :
    abelianGradedSub A M i (p + q) p = q := by
  apply Prod.ext
  · change ((show A.Q.obj i from p.1) + (show A.Q.obj i from q.1)) -
      (show A.Q.obj i from p.1) = (show A.Q.obj i from q.1)
    exact add_sub_cancel_left
      (show A.Q.obj i from p.1) (show A.Q.obj i from q.1)
  · simp [abelianGradedSub]

theorem abelianGradedSub_sub_cancel_left (i : I)
    (p q : (A.toObservationSystem.gradedObservation M).obj i) :
    abelianGradedSub A M i p (abelianGradedSub A M i p q) = q := by
  apply Prod.ext
  · change (show A.Q.obj i from p.1) -
      ((show A.Q.obj i from p.1) - (show A.Q.obj i from q.1)) =
        (show A.Q.obj i from q.1)
    exact sub_sub_cancel
      (show A.Q.obj i from p.1) (show A.Q.obj i from q.1)
  · simp [abelianGradedSub]

theorem abelianGradedSub_add_cancel_self (i : I)
    (p q : (A.toObservationSystem.gradedObservation M).obj i) :
    abelianGradedSub A M i p q + q = p := by
  apply Prod.ext
  · change ((show A.Q.obj i from p.1) - (show A.Q.obj i from q.1)) +
      (show A.Q.obj i from q.1) = (show A.Q.obj i from p.1)
    exact sub_add_cancel
      (show A.Q.obj i from p.1) (show A.Q.obj i from q.1)
  · simp [abelianGradedSub]

/-- The fixed translation `y = Q̃(u)x - a` from a composite source
requirement to the source requirement of the second correction. -/
def translationSecondRequired
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k)
    (x : A.toObservationSystem.Required M (φ.comp ψ)) :
    A.toObservationSystem.Required M ψ :=
  ⟨abelianGradedSub A M j
      ((A.toObservationSystem.gradedObservation M).map φ.base x.1) φ.label, by
    have hmapcomp := ConcreteCategory.congr_hom
      ((A.toObservationSystem.gradedObservation M).map_comp φ.base ψ.base)
    have hx :
        (A.toObservationSystem.gradedObservation M).map ψ.base
            ((A.toObservationSystem.gradedObservation M).map φ.base x.1) =
          (A.toObservationSystem.gradedObservation M).map ψ.base φ.label +
            ψ.label := by
      rw [← CategoryTheory.comp_apply]
      rw [← hmapcomp]
      exact x.condition
    rw [gradedMap_abelianGradedSub, hx]
    exact abelianGradedSub_add_cancel A M k _ _⟩

/-- The public canonical translation from the composite required fibre to the
second required fibre. -/
def translationCertificate
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k) :
    A.toObservationSystem.Required M (φ.comp ψ) →
      A.toObservationSystem.Required M ψ :=
  translationSecondRequired A M φ ψ

/-- After choosing the second realizer, the fixed translation
`z = x - ρ_i W(r)` lies in the first required fibre. -/
def translationFirstRequired
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k)
    (x : A.toObservationSystem.Required M (φ.comp ψ))
    (r : A.toObservationSystem.UniversalRealizer M W g ψ)
    (hr : r.required = translationCertificate A M φ ψ x) :
    A.toObservationSystem.Required M φ :=
  ⟨abelianGradedSub A M i x.1
      (A.toObservationSystem.physicalObservation M W g i r.state), by
    rw [gradedMap_abelianGradedSub]
    rw [A.toObservationSystem.physicalObservation_naturality M W g φ.base]
    rw [r.observation_eq]
    rw [hr]
    exact abelianGradedSub_sub_cancel_left A M j _ _⟩

/-- The canonical binary compatible realizer selected by the two translated
required fibres. -/
def translatedCompatibleRealizer
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k)
    (F R : PhysicalFamily (FiniteComponentState G Θ))
    (hcompatible : AllCompatible F R)
    (rr : A.toObservationSystem.FamilyRealizer M W g R ψ)
    (rf : A.toObservationSystem.FamilyRealizer M W g F φ) :
    CompatibleRealizer (O := A.toObservationSystem)
      (M := M) (W := W) (g := g)
      (binaryCorrectionString φ ψ)
      (binaryCorrectionFamilies φ ψ F R) where
  val
    | .inl _ => rf
    | .inr (.inl _) => rr
    | .inr (.inr a) => nomatch a.down
  property := by
    rw [allCompatible_iff] at hcompatible
    have hc := hcompatible rf.branch rr.branch
    rw [rf.family_state_eq, rr.family_state_eq] at hc
    have h := (naryCompatible_reindex
      (binaryCorrectionIndexEquiv φ ψ)
      (binaryStateFamily rf.universal.state rr.universal.state)).2
        hc
    convert h using 1
    funext a
    rcases a with a | a
    · rfl
    · rcases a with a | a
      · rfl
      · exact nomatch a.down

/-- The abelian translation certificate: two covering families with
whole-family cross-compatibility give a cover of their binary physical sums
for the fixed Grothendieck composite correction. -/
theorem covers_comp_of_allCompatible
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k)
    (F R : PhysicalFamily (FiniteComponentState G Θ))
    (hF : A.toObservationSystem.Covers M W g F φ)
    (hR : A.toObservationSystem.Covers M W g R ψ)
    (hcompatible : AllCompatible F R) :
    A.toObservationSystem.Covers M W g
      (compatibleRealizerSumFamily (O := A.toObservationSystem)
        (M := M) (W := W) (g := g)
        (binaryCorrectionString φ ψ)
        (binaryCorrectionFamilies φ ψ F R))
      (binaryCorrectionString φ ψ).composite := by
  apply (naryCompositionCriterion
    (O := A.toObservationSystem) (M := M) (W := W) (g := g)
    (binaryCorrectionString φ ψ)
    (binaryCorrectionFamilies φ ψ F R)).2
  intro target
  let targetComp : A.toObservationSystem.Required M (φ.comp ψ) :=
    ⟨target.1, by simpa using target.2⟩
  let y := translationCertificate A M φ ψ targetComp
  obtain ⟨rr, hrr⟩ := hR y
  have hrr' : rr.universal.required = y := hrr
  let z := translationFirstRequired A M W g φ ψ targetComp rr.universal hrr'
  obtain ⟨rf, hrf⟩ := hF z
  let r := translatedCompatibleRealizer A M W g φ ψ F R
    hcompatible rr rf
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change A.toObservationSystem.physicalObservation M W g i
      (compatibleRealizerState
        (O := A.toObservationSystem) (M := M) (W := W) (g := g) r) =
      target.1
  rw [compatibleRealizerState]
  rw [A.toObservationSystem.physicalObservation_finitePhysicalUnion]
  rw [sum_binaryCorrectionIndex φ ψ]
  change A.toObservationSystem.physicalObservation M W g i rf.universal.state +
      A.toObservationSystem.physicalObservation M W g i rr.universal.state =
        target.1
  rw [rf.universal.observation_eq]
  have hrf' : rf.universal.required = z := hrf
  rw [hrf']
  exact abelianGradedSub_add_cancel_self A M i _ _

end ObservationSystem

end Erdos289
