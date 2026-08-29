import Universal.Correction.Realizer
import Universal.NaryCompatibility

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Sum

/-!
# Finite physical composition of corrections

This module translates the finite-string construction fixed in the
specification.  Its compatible-realizer object is the pullback of the product
of the individual family realizers along the direct n-ary physical domain.
No parenthesization is part of the public data.
-/

open CategoryTheory
open scoped BigOperators

namespace Erdos289

universe u v w x y

namespace ObservationSystem

variable {I : Type u} [Category.{v} I]
variable {Γ : Type w} [AddCommMonoid Γ]
variable (O : ObservationSystem I Γ)
variable (M : Type x) [AddCommMonoid M]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : PhysicalAdditiveMap G Θ Γ)
variable (g : PhysicalAdditiveMap G Θ M)

/-- A finite composable string of corrections, with its endpoints in the
type. -/
inductive CorrectionString : I → I → Type (max u v w x)
  | nil (i : I) : CorrectionString i i
  | cons {i j k : I} (head : O.Correction M i j)
      (tail : CorrectionString j k) : CorrectionString i k

namespace CorrectionString

variable {O M}

/-- The finite position type of a correction string. -/
@[reducible]
def Index {i j : I} : O.CorrectionString M i j → Type u
  | .nil _ => ULift.{u} Empty
  | .cons _ tail => ULift.{u} Unit ⊕ tail.Index

noncomputable instance {i j : I} (s : O.CorrectionString M i j) :
    Fintype s.Index := by
  induction s with
  | nil => dsimp [Index]; infer_instance
  | cons head tail ih =>
      dsimp [Index]
      letI : Fintype tail.Index := ih
      infer_instance

/-- An arrow of the correction category with its endpoints retained. -/
structure Arrow where
  source : I
  target : I
  correction : O.Correction M source target

/-- The correction at a position of a composable string. -/
@[reducible]
def arrow {i j : I} (s : O.CorrectionString M i j) :
    s.Index → Arrow (O := O) (M := M) :=
  match s with
  | .nil _ => fun x ↦ nomatch x.down
  | .cons head tail =>
      Sum.elim (fun _ ↦ ⟨_, _, head⟩) tail.arrow

/-- The fixed Grothendieck composite of a correction string. -/
noncomputable def composite {i j : I} :
    O.CorrectionString M i j → O.Correction M i j
  | .nil i => Correction.id (O := O) (M := M) i
  | .cons head tail => head.comp tail.composite

/-- Additivity and naturality identify the observation of the physical sum
with the label of the fixed Grothendieck composite. -/
theorem map_observation_sum_eq_composite_label
    {i j : I} (s : O.CorrectionString M i j)
    (state : s.Index → FiniteComponentState G Θ)
    (required : ∀ a, O.Required M (s.arrow a).correction)
    (hobservation : ∀ a,
      O.physicalObservation M W g (s.arrow a).source (state a) =
        (required a).1) :
    (O.gradedObservation M).map s.composite.base
        (∑ a, O.physicalObservation M W g i (state a)) =
      s.composite.label := by
  induction s with
  | nil i =>
      simp [composite]
  | @cons i k j head tail ih =>
      simp only [Index] at state required hobservation ⊢
      rw [show (CorrectionString.composite (.cons head tail)).base =
        head.base ≫ tail.composite.base by rfl]
      have hmapcomp := ConcreteCategory.congr_hom
        ((O.gradedObservation M).map_comp head.base tail.composite.base)
      rw [hmapcomp]
      rw [CategoryTheory.comp_apply]
      change (O.gradedObservation M).map tail.composite.base
        ((O.gradedObservation M).map head.base
          (∑ a, O.physicalObservation M W g i (state a))) =
            (CorrectionString.composite (.cons head tail)).label
      rw [Fintype.sum_sum_type, Fintype.sum_unique]
      rw [map_add]
      have hhead :
          (O.gradedObservation M).map head.base
              (O.physicalObservation M W g i
                (state (.inl (ULift.up Unit.unit)))) =
            head.label := by
        have hobs := hobservation (.inl (ULift.up Unit.unit))
        change O.physicalObservation M W g i
            (state (.inl (ULift.up Unit.unit))) =
          (required (.inl (ULift.up Unit.unit))).1 at hobs
        rw [hobs]
        exact (required (.inl (ULift.up Unit.unit))).condition
      rw [hhead]
      have htailObs : ∀ a,
          O.physicalObservation M W g (tail.arrow a).source (state (.inr a)) =
            (required (.inr a)).1 :=
        fun a ↦ hobservation (.inr a)
      have hnat : ∀ a,
          (O.gradedObservation M).map head.base
              (O.physicalObservation M W g i (state (.inr a))) =
            O.physicalObservation M W g k (state (.inr a)) :=
        fun a ↦ O.physicalObservation_naturality M W g head.base _
      rw [map_sum]
      simp_rw [hnat]
      rw [map_add, ih (fun a ↦ state (.inr a))
        (fun a ↦ required (.inr a)) htailObs]
      rfl

end CorrectionString

variable {O M W g}

/-- Families attached to all entries of a correction string. -/
abbrev CorrectionFamilies {i j : I} (s : O.CorrectionString M i j) :=
  ∀ _a : s.Index, PhysicalFamily (FiniteComponentState G Θ)

/-- The product of the individual family realizers restricted by the direct
n-ary physical compatibility locus. -/
def CompatibleRealizer {i j : I} (s : O.CorrectionString M i j)
    (F : CorrectionFamilies (G := G) (Θ := Θ) s) :=
  {r : ∀ a, O.FamilyRealizer M W g (F a) (s.arrow a).correction //
    NaryCompatible (fun a ↦ (r a).universal.state)}

/-- The direct n-ary physical state underlying compatible realizers. -/
noncomputable def compatibleRealizerState {i j : I}
    {s : O.CorrectionString M i j}
    {F : CorrectionFamilies (G := G) (Θ := Θ) s}
    (r : CompatibleRealizer (O := O) (M := M) (W := W) (g := g) s F) :
    FiniteComponentState G Θ :=
  finitePhysicalUnion
    (⟨fun a ↦ (r.1 a).universal.state, r.2⟩ :
      NaryPhysicalDomain G Θ s.Index)

/-- The canonical map from compatible realizers to the required fibre of the
composite correction. -/
noncomputable def compatibleRealizerMap {i j : I}
    (s : O.CorrectionString M i j)
    (F : CorrectionFamilies (G := G) (Θ := Θ) s) :
    CompatibleRealizer (O := O) (M := M) (W := W) (g := g) s F →
      O.Required M s.composite :=
  fun r ↦
    ⟨O.physicalObservation M W g i
        (compatibleRealizerState (O := O) (M := M) (W := W) (g := g) r),
      by
        let S : NaryPhysicalDomain G Θ s.Index :=
          ⟨fun a ↦ (r.1 a).universal.state, r.2⟩
        change (O.gradedObservation M).map s.composite.base
          (O.physicalObservation M W g i (finitePhysicalUnion S)) =
            s.composite.label
        calc
          _ = (O.gradedObservation M).map s.composite.base
              (∑ a, O.physicalObservation M W g i (S.1 a)) :=
            congrArg ((O.gradedObservation M).map s.composite.base)
              (O.physicalObservation_finitePhysicalUnion M W g i S)
          _ = s.composite.label :=
            CorrectionString.map_observation_sum_eq_composite_label
              (O := O) (M := M) (W := W) (g := g) s
              (fun a ↦ (r.1 a).universal.state)
              (fun a ↦ (r.1 a).required)
              (fun a ↦ (r.1 a).universal.observation_eq)⟩

/-- The physical family of direct n-ary sums indexed by compatible
realizers. -/
noncomputable def compatibleRealizerSumFamily {i j : I}
    (s : O.CorrectionString M i j)
    (F : CorrectionFamilies (G := G) (Θ := Θ) s) :
    PhysicalFamily (FiniteComponentState G Θ) where
  left := CompatibleRealizer (O := O) (M := M) (W := W) (g := g) s F
  hom := compatibleRealizerState

/-- Finite-string composition criterion: the direct n-ary physical sums cover
the composite exactly when the canonical compatible-realizer map is regular
epimorphic, expressed here by surjectivity in the fixed category `Type`. -/
theorem naryCompositionCriterion {i j : I}
    (s : O.CorrectionString M i j)
    (F : CorrectionFamilies (G := G) (Θ := Θ) s) :
    O.Covers M W g
        (compatibleRealizerSumFamily (O := O) (M := M) (W := W) (g := g) s F)
        s.composite ↔
      Function.Surjective
        (compatibleRealizerMap (O := O) (M := M) (W := W) (g := g) s F) := by
  constructor
  · intro h target
    obtain ⟨r, hr⟩ := h target
    refine ⟨r.branch, ?_⟩
    apply Subtype.ext
    rw [← hr]
    change O.physicalObservation M W g i
        ((compatibleRealizerSumFamily
          (O := O) (M := M) (W := W) (g := g) s F).hom r.branch) =
      r.required.1
    rw [r.family_state_eq]
    exact r.universal.observation_eq
  · intro h target
    obtain ⟨branch, hbranch⟩ := h target
    refine ⟨{
      left := branch
      right := {
        left := compatibleRealizerState
          (O := O) (M := M) (W := W) (g := g) branch
        right := target
        condition := ?_ }
      condition := rfl }, ?_⟩
    · rw [← hbranch]
      rfl
    · rfl

/-- Invariant form of the finite-string composition criterion. -/
theorem naryCompositionCriterion_regularEpi {i j : I}
    (s : O.CorrectionString M i j)
    (F : CorrectionFamilies (G := G) (Θ := Θ) s) :
    O.Covers M W g
        (compatibleRealizerSumFamily (O := O) (M := M) (W := W) (g := g) s F)
        s.composite ↔
      TypeRegularEpi
        (compatibleRealizerMap (O := O) (M := M) (W := W) (g := g) s F) := by
  rw [naryCompositionCriterion]
  exact (type_regularEpi_iff_surjective _).symm

/-- The two-entry correction string used by the binary specialization. -/
def binaryCorrectionString {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k) :
    O.CorrectionString M i k :=
  .cons φ (.cons ψ (.nil k))

/-- The two physical families attached to the two-entry correction string. -/
def binaryCorrectionFamilies {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k)
    (F R : PhysicalFamily (FiniteComponentState G Θ)) :
    CorrectionFamilies (G := G) (Θ := Θ) (binaryCorrectionString φ ψ)
  | .inl _ => F
  | .inr (.inl _) => R
  | .inr (.inr a) => nomatch a.down

/-- The canonical identification of the two-entry string positions with
`Fin 2`. -/
def binaryCorrectionIndexEquiv {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k) :
    (binaryCorrectionString φ ψ).Index ≃ Fin 2 where
  toFun
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr a) => nomatch a.down
  invFun n := if n = 0
    then .inl (ULift.up Unit.unit)
    else .inr (.inl (ULift.up Unit.unit))
  left_inv a := by
    rcases a with a | a
    · apply congrArg Sum.inl
      exact Subsingleton.elim _ _
    · rcases a with a | a
      · apply congrArg Sum.inr
        apply congrArg Sum.inl
        exact Subsingleton.elim _ _
      · exact nomatch a.down
  right_inv n := by
    fin_cases n <;> simp

@[simp]
theorem binaryCorrectionString_composite {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k) :
    (binaryCorrectionString φ ψ).composite = φ.comp ψ := by
  simp [binaryCorrectionString, CorrectionString.composite]

theorem sum_binaryCorrectionIndex {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k)
    {A : Type y} [AddCommMonoid A]
    (f : (binaryCorrectionString φ ψ).Index → A) :
    ∑ a, f a =
      f (.inl (ULift.up Unit.unit)) +
        f (.inr (.inl (ULift.up Unit.unit))) := by
  let e := binaryCorrectionIndexEquiv φ ψ
  calc
    ∑ a, f a = ∑ n : Fin 2, f (e.symm n) :=
      Fintype.sum_equiv e f _
        (fun a ↦ congrArg f (e.symm_apply_apply a).symm)
    _ = f (.inl (ULift.up Unit.unit)) +
          f (.inr (.inl (ULift.up Unit.unit))) := by
      rw [Fin.sum_univ_two]
      rfl

/-- Binary specialization of the finite-string composition criterion. -/
theorem binaryCompositionCriterion {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k)
    (F : CorrectionFamilies (G := G) (Θ := Θ)
      (binaryCorrectionString φ ψ)) :
    O.Covers M W g
        (compatibleRealizerSumFamily (O := O) (M := M) (W := W) (g := g)
          (binaryCorrectionString φ ψ) F)
        (binaryCorrectionString φ ψ).composite ↔
      Function.Surjective
        (compatibleRealizerMap (O := O) (M := M) (W := W) (g := g)
          (binaryCorrectionString φ ψ) F) :=
  naryCompositionCriterion _ _

/-- Binary specialization of the invariant regular-epimorphism criterion. -/
theorem binaryCompositionCriterion_regularEpi {i j k : I}
    (φ : O.Correction M i j) (ψ : O.Correction M j k)
    (F : CorrectionFamilies (G := G) (Θ := Θ)
      (binaryCorrectionString φ ψ)) :
    O.Covers M W g
        (compatibleRealizerSumFamily (O := O) (M := M) (W := W) (g := g)
          (binaryCorrectionString φ ψ) F)
        (binaryCorrectionString φ ψ).composite ↔
      TypeRegularEpi
        (compatibleRealizerMap (O := O) (M := M) (W := W) (g := g)
          (binaryCorrectionString φ ψ) F) :=
  naryCompositionCriterion_regularEpi _ _

end ObservationSystem

end Erdos289
