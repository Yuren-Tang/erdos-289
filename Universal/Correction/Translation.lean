import Universal.Correction.Composition

import Mathlib.Algebra.Category.Grp.Basic

/-!
# Abelian translation certificate

The abelian specialization is recorded before forgetting to commutative
monoids.  Subtraction is used only in the observation coordinate; the grading
coordinate remains in the fixed commutative grading monoid.
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
variable (M : Type x) [AddCommMonoid M]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : PhysicalAdditiveMap G Θ Γ)
variable (g : PhysicalAdditiveMap G Θ M)
variable {i j k : I}

/-- The fixed translation `y = Q̃(u)x - a` from a composite source
requirement to the source requirement of the second correction, with grade
coordinate supplied by the second correction label. -/
def translationSecondRequired
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k)
    (x : A.toObservationSystem.Required M (φ.comp ψ)) :
    A.toObservationSystem.Required M ψ :=
  ⟨(((show A.Q.obj j from
        ((A.toObservationSystem.gradedObservation M).map φ.base x.1).1) -
      (show A.Q.obj j from φ.label.1)), ψ.label.2), by
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
    apply Prod.ext
    · have hxQ := congrArg Prod.fst hx
      change (A.Q.map ψ.base)
          ((show A.Q.obj j from
              ((A.toObservationSystem.gradedObservation M).map φ.base x.1).1) -
            (show A.Q.obj j from φ.label.1)) =
        (show A.Q.obj k from ψ.label.1)
      rw [map_sub (A.Q.map ψ.base).hom]
      change (A.Q.map ψ.base)
          (show A.Q.obj j from
            ((A.toObservationSystem.gradedObservation M).map φ.base x.1).1) =
        (A.Q.map ψ.base) (show A.Q.obj j from φ.label.1) +
          (show A.Q.obj k from ψ.label.1) at hxQ
      rw [hxQ]
      exact add_sub_cancel_left _ _
    · rfl⟩

/-- The public canonical translation from the composite required fibre to the
second required fibre. -/
def translationCertificate
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k) :
    A.toObservationSystem.Required M (φ.comp ψ) →
      A.toObservationSystem.Required M ψ :=
  translationSecondRequired A M φ ψ

/-- After choosing the second realizer, the fixed translation
`z = (x_Q - ρ_i W(r), m)` lies in the first required fibre, where `m`
is the first correction's grade label. -/
def translationFirstRequired
    (φ : A.toObservationSystem.Correction M i j)
    (ψ : A.toObservationSystem.Correction M j k)
    (x : A.toObservationSystem.Required M (φ.comp ψ))
    (r : A.toObservationSystem.UniversalRealizer M W g ψ)
    (hr : r.required = translationCertificate A M φ ψ x) :
    A.toObservationSystem.Required M φ :=
  ⟨(((show A.Q.obj i from x.1.1) -
      (show A.Q.obj i from
        (A.toObservationSystem.physicalObservation M W g i r.state).1)),
      φ.label.2), by
    apply Prod.ext
    · have hnat := congrArg Prod.fst
        (A.toObservationSystem.physicalObservation_naturality M W g
          φ.base r.state)
      have hobs := congrArg Prod.fst r.observation_eq
      have hreq := congrArg (fun q ↦ q.val.1) hr
      change (A.Q.map φ.base)
          ((show A.Q.obj i from x.1.1) -
            (show A.Q.obj i from
              (A.toObservationSystem.physicalObservation M W g i r.state).1)) =
        (show A.Q.obj j from φ.label.1)
      rw [map_sub (A.Q.map φ.base).hom]
      change (A.Q.map φ.base) (show A.Q.obj i from
          (A.toObservationSystem.physicalObservation M W g i r.state).1) =
        (show A.Q.obj j from
          (A.toObservationSystem.physicalObservation M W g j r.state).1) at hnat
      rw [hnat]
      change (show A.Q.obj j from
          (A.toObservationSystem.physicalObservation M W g j r.state).1) =
        (show A.Q.obj j from r.required.val.1) at hobs
      rw [hobs]
      change (show A.Q.obj j from r.required.val.1) =
        (show A.Q.obj j from
          (translationCertificate A M φ ψ x).val.1) at hreq
      rw [hreq]
      change (A.Q.map φ.base) (show A.Q.obj i from x.1.1) -
          ((A.Q.map φ.base) (show A.Q.obj i from x.1.1) -
            (show A.Q.obj j from φ.label.1)) =
        (show A.Q.obj j from φ.label.1)
      exact sub_sub_cancel _ _
    · rfl⟩

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
  apply Prod.ext
  · change ((show A.Q.obj i from target.1.1) -
        (show A.Q.obj i from
          (A.toObservationSystem.physicalObservation M W g i
            rr.universal.state).1)) +
        (show A.Q.obj i from
          (A.toObservationSystem.physicalObservation M W g i
            rr.universal.state).1) =
      (show A.Q.obj i from target.1.1)
    exact sub_add_cancel _ _
  · have hnat := congrArg Prod.snd
        (A.toObservationSystem.physicalObservation_naturality M W g
          φ.base rr.universal.state)
    have hobs := congrArg Prod.snd rr.universal.observation_eq
    have hreq := congrArg (fun q ↦ q.val.2) hrr'
    have htarget := congrArg Prod.snd targetComp.condition
    change (A.toObservationSystem.physicalObservation M W g i
        rr.universal.state).2 =
      (A.toObservationSystem.physicalObservation M W g j
        rr.universal.state).2 at hnat
    change (A.toObservationSystem.physicalObservation M W g j
        rr.universal.state).2 = rr.universal.required.val.2 at hobs
    change rr.universal.required.val.2 = ψ.label.2 at hreq
    change target.1.2 = φ.label.2 + ψ.label.2 at htarget
    change φ.label.2 +
        (A.toObservationSystem.physicalObservation M W g i
          rr.universal.state).2 = target.1.2
    rw [hnat, hobs, hreq, htarget]

end ObservationSystem

end Erdos289
