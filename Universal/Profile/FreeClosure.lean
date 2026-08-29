import Universal.Profile.GradeResource
import Universal.Profile.BoundSaturation
import Universal.Correction.Composition
import Universal.Target.CompactResolution

import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Reflected free paths and physical realization

This module keeps path formation independent of chosen parenthesizations.
Physical realization is defined by the frozen finite-family, zero-cover, and
branchwise-resource witness object.
-/

open CategoryTheory
open QuotientAddGroup

namespace Erdos289

universe u v w z

/-- The compact quotient resolution as the observation system used by the
physical profile interface. -/
def compactProfileObservationSystem
    {Γ : Type u} [AddCommGroup Γ] (t : Marking Γ) :
    ObservationSystem (CompactStage t) Γ where
  Q := compactResolution t ⋙ forget₂ AddCommGrpCat AddCommMonCat
  rho := {
    app := fun H ↦ AddCommMonCat.ofHom
      ((QuotientAddGroup.mk' H.1).comp (markingQuotient t))
    naturality := fun H K f ↦ by
      apply AddCommMonCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      rfl }

namespace ObservationSystem

variable {Γ : Type u} [AddCommGroup Γ] {t : Marking Γ}
variable {M : Type v} [AddCommMonoid M]
variable {U : Type w} [AddCommMonoid U] [PartialOrder U] [IsOrderedAddMonoid U]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : PhysicalAdditiveMap G Θ Γ)
variable (g : PhysicalAdditiveMap G Θ M)
variable (μ : PhysicalAdditiveMap G Θ U)

private abbrev profileO := compactProfileObservationSystem t

/-- The simple zero correction attached to a compact-stage arrow and exact
grade. -/
def profileZeroSection {H K : CompactStage t} (a : H ⟶ K) (m : M) :
    profileO.Correction M H K where
  base := a
  label := (0, m)

/-- U7.5 physical bound witness: a finite physical family, a cover of the
simple zero correction, and a branchwise resource bound. -/
structure PhysWitness {H K : CompactStage t} (a : H ⟶ K) (m : M) (u : U) where
  family : FinitePhysicalFamily.{u, u} (FiniteComponentState G Θ)
  cover : profileO.Covers M W g family.family (profileZeroSection a m)
  resource_bound : ∀ b : family.family.left, μ (family.family.hom b) ≤ u

/-- The cover field is the invariant regular epimorphism required by the
frozen interface, through the canonical fixed-`Type` bridge. -/
theorem PhysWitness.cover_regularEpi {H K : CompactStage t} {a : H ⟶ K}
    {m : M} {u : U} (w : PhysWitness W g μ a m u) :
    TypeRegularEpi
      (FamilyRealizer.required :
        profileO.FamilyRealizer M W g w.family.family (profileZeroSection a m) →
          profileO.Required M (profileZeroSection a m)) :=
  ((profileO.covers_iff_regularEpi M W g w.family.family
    (profileZeroSection a m)).1 w.cover)

/-- The raw set of physically realized grade-resource labels. -/
def PhysRaw {H K : CompactStage t} (a : H ⟶ K) :
    Set (GradeResourceLabel M U) :=
  {r | Nonempty (PhysWitness W g μ a r.1 r.2)}

/-- The same witness realizes every weaker resource bound. -/
theorem physRaw_resource_upper {H K : CompactStage t} {a : H ⟶ K}
    {m : M} {u u' : U} (h : u ≤ u') :
    (m, u) ∈ PhysRaw W g μ a → (m, u') ∈ PhysRaw W g μ a := by
  rintro ⟨w⟩
  exact ⟨{ w with resource_bound := fun b ↦ (w.resource_bound b).trans h }⟩

/-- The raw physical realization set is a fixed point of bound saturation. -/
theorem physRaw_isClosed {H K : CompactStage t} (a : H ⟶ K) :
    (boundSaturationClosure (M := M) (U := U)).IsClosed (PhysRaw W g μ a) := by
  rw [(boundSaturationClosure (M := M) (U := U)).isClosed_iff]
  apply Set.Subset.antisymm
  · rintro ⟨m, u'⟩ ⟨⟨m₀, u⟩, hr, hm, hu⟩
    dsimp [ResourceBoundLE] at hm hu
    subst m₀
    exact physRaw_resource_upper W g μ hu hr
  · exact subset_boundSaturation _

/-- The canonical bound profile of physical realizations. -/
def Phys {H K : CompactStage t} (a : H ⟶ K) : BoundProfile M U :=
  ⟨PhysRaw W g μ a, physRaw_isClosed W g μ a⟩

@[simp]
theorem mem_phys_iff {H K : CompactStage t} (a : H ⟶ K)
    (r : GradeResourceLabel M U) :
    r ∈ (Phys W g μ a : Set (GradeResourceLabel M U)) ↔
      Nonempty (PhysWitness W g μ a r.1 r.2) :=
  Iff.rfl

end ObservationSystem

section FreePaths

variable {X : Type u} [Quiver.{z} X]
variable {M : Type v} [AddCommMonoid M]
variable {U : Type w} [AddCommMonoid U] [PartialOrder U] [IsOrderedAddMonoid U]

/-- Reflected tensor product of the edge profiles along a finite path. -/
noncomputable def pathTensor
    (P : ∀ {x y : X}, (x ⟶ y) → BoundProfile M U) :
    ∀ {x y : X}, Quiver.Path x y → BoundProfile M U
  | _, _, .nil => 0
  | _, _, .cons p e => pathTensor P p + P e

/-- The unreflected label locus at the final path-tensor step.  Its elements
are literal finite tuple sums; reflection adds only resource weakening. -/
def pathRawLabels
    (P : ∀ {x y : X}, (x ⟶ y) → BoundProfile M U) :
    ∀ {x y : X}, Quiver.Path x y → Set (GradeResourceLabel M U)
  | _, _, .nil => {0}
  | _, _, .cons p e =>
      pathRawLabels P p +
        (P e : Set (GradeResourceLabel M U))

/-- Every path tensor is exactly the reflection of its literal tuple-sum
locus. -/
theorem pathTensor_coe
    (P : ∀ {x y : X}, (x ⟶ y) → BoundProfile M U)
    {x y : X} (p : Quiver.Path x y) :
    (pathTensor P p : Set (GradeResourceLabel M U)) =
      boundSaturation (pathRawLabels P p) := by
  cases p with
  | nil =>
      simp only [pathTensor, pathRawLabels]
      exact boundProfile_zero_coe
  | cons p e =>
      simp only [pathTensor, pathRawLabels]
      change ((pathTensor P p + P e : BoundProfile M U) :
          Set (GradeResourceLabel M U)) =
        boundSaturation
          (pathRawLabels P p +
            (P e : Set (GradeResourceLabel M U)))
      rw [boundProfile_add_coe, pathTensor_coe]
      exact boundSaturation_add_left _ _

/-- U7.6: the free enriched hom is the join of the reflected tensors over
all finite paths. -/
noncomputable def freePathProfile
    (P : ∀ {x y : X}, (x ⟶ y) → BoundProfile M U)
    (x y : X) : BoundProfile M U :=
  ⨆ p : Quiver.Path x y, pathTensor P p

theorem freePathProfile_characterization
    (P : ∀ {x y : X}, (x ⟶ y) → BoundProfile M U)
    (x y : X) :
    freePathProfile P x y = ⨆ p : Quiver.Path x y, pathTensor P p :=
  rfl

end FreePaths

section PhysicalTransfer

variable {Γ : Type u} [AddCommGroup Γ] {t : Marking Γ}
variable {M : Type v} [AddCommMonoid M]
variable {U : Type w} [AddCommMonoid U] [PartialOrder U] [IsOrderedAddMonoid U]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : ObservationSystem.PhysicalAdditiveMap G Θ Γ)
variable (g : ObservationSystem.PhysicalAdditiveMap G Θ M)
variable (μ : ObservationSystem.PhysicalAdditiveMap G Θ U)

/-- The mechanistic finite-composition data attached to one literal tuple of
edge labels.  The entries are the edge-local physical families; their direct
n-ary compatible union is required to satisfy the frozen regular-epimorphism
criterion.  In particular, no composite `PhysWitness` is assumed here. -/
structure PathwiseCompositionData
    {H K : CompactStage t} (p : Quiver.Path H K) (m : M) (u : U) where
  string : (compactProfileObservationSystem t).CorrectionString M H K
  families : ∀ _a : string.Index,
    PhysicalFamily.{u, u} (FiniteComponentState G Θ)
  finite_compatible : Finite (ObservationSystem.CompatibleRealizer
    (O := compactProfileObservationSystem t) (M := M) (W := W) (g := g)
    string families)
  local_cover : ∀ a, (compactProfileObservationSystem t).Covers M W g
    (families a) (string.arrow a).correction
  localBound : string.Index → U
  local_resource_bound : ∀ a b,
    μ ((families a).hom b) ≤ localBound a
  total_resource_bound : (∑ a, localBound a) ≤ u
  composite_eq : string.composite =
    ObservationSystem.profileZeroSection (t := t)
      (CategoryTheory.composePath p) m
  compatible_regularEpi : TypeRegularEpi
    (ObservationSystem.compatibleRealizerMap
      (O := compactProfileObservationSystem t) (M := M) (W := W) (g := g)
      string families)

/-- A pathwise physical-composition certificate.  For each literal tuple of
edge labels it supplies edge-local realizers and the regular-epimorphic
compatible-realizer comparison required by the frozen composition spine. -/
structure PathwisePhysicalCertificate
    (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U) where
  realize_raw : ∀ {H K : CompactStage t} (p : Quiver.Path H K)
    (r : GradeResourceLabel M U),
    r ∈ pathRawLabels P p →
      Nonempty (PathwiseCompositionData W g μ p r.1 r.2)

/-- The frozen regular-epimorphic n-ary composition criterion turns the
pathwise edge-local data into the composite physical witness. -/
noncomputable def PathwiseCompositionData.toPhysWitness
    {H K : CompactStage t} {p : Quiver.Path H K} {m : M} {u : U}
    (d : PathwiseCompositionData W g μ p m u) :
    ObservationSystem.PhysWitness W g μ
      (CategoryTheory.composePath p) m u := by
  let O := compactProfileObservationSystem t
  let F := ObservationSystem.compatibleRealizerSumFamily
    (O := O) (M := M) (W := W) (g := g) d.string d.families
  letI : Finite F.left := d.finite_compatible
  letI : Fintype F.left := Fintype.ofFinite F.left
  let e := Fintype.equivFin F.left
  let Fsmall : PhysicalFamily.{u, u} (FiniteComponentState G Θ) := {
    left := ULift.{u} (Fin (Fintype.card F.left))
    hom := fun n ↦ F.hom (e.symm n.down) }
  refine {
    family := ⟨Fsmall, inferInstanceAs
      (Finite (ULift.{u} (Fin (Fintype.card F.left))))⟩
    cover := ?_
    resource_bound := ?_ }
  · have hcover : O.Covers M W g F d.string.composite :=
      (ObservationSystem.naryCompositionCriterion_regularEpi
      (O := O) (M := M) (W := W) (g := g)
      d.string d.families).2 d.compatible_regularEpi
    rw [d.composite_eq] at hcover
    change O.Covers M W g Fsmall
      (ObservationSystem.profileZeroSection (t := t)
        (CategoryTheory.composePath p) m)
    intro target
    obtain ⟨r, hr⟩ := hcover target
    refine ⟨{
      left := ULift.up (e r.branch)
      right := r.universal
      condition := ?_ }, hr⟩
    change F.hom (e.symm (e r.branch)) = r.universal.state
    rw [e.symm_apply_apply]
    exact r.family_state_eq
  · intro n
    let b := e.symm n.down
    calc
      μ (Fsmall.hom n) = ∑ a, μ ((b.1 a).universal.state) := by
        exact μ.map_finitePhysicalUnion
          (⟨fun a ↦ (b.1 a).universal.state, b.2⟩ :
            NaryPhysicalDomain G Θ d.string.Index)
      _ = ∑ a, μ ((d.families a).hom ((b.1 a).branch)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [(b.1 a).family_state_eq]
      _ ≤ ∑ a, d.localBound a := by
        exact Finset.sum_le_sum fun a _ ↦
          d.local_resource_bound a ((b.1 a).branch)
      _ ≤ u := d.total_resource_bound

/-- Each certified path tensor is contained in physical realization. -/
theorem pathTensor_le_phys
    (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U)
    (cert : PathwisePhysicalCertificate W g μ P)
    {H K : CompactStage t} (p : Quiver.Path H K) :
    pathTensor P p ≤ ObservationSystem.Phys W g μ
      (CategoryTheory.composePath p) := by
  intro r hr
  rw [pathTensor_coe] at hr
  rcases r with ⟨m, u'⟩
  rcases hr with ⟨⟨m₀, u⟩, hraw, hm, hu⟩
  dsimp [ResourceBoundLE] at hm hu
  subst m₀
  exact ObservationSystem.physRaw_resource_upper W g μ hu <| by
    rcases cert.realize_raw p (m, u) hraw with ⟨d⟩
    exact ⟨d.toPhysWitness W g μ⟩

/-- Thinness of the compact-stage category identifies the path composite
with the specified endpoint arrow. -/
theorem pathTensor_le_phys_arrow
    (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U)
    (cert : PathwisePhysicalCertificate W g μ P)
    {H K : CompactStage t} (a : H ⟶ K) (p : Quiver.Path H K) :
    pathTensor P p ≤ ObservationSystem.Phys W g μ a := by
  simpa only [Subsingleton.elim (CategoryTheory.composePath p) a] using
    pathTensor_le_phys W g μ P cert p

/-- U7.7: joining the pathwise regular-epimorphic physical certificates
transfers the entire free enriched hom into physical realization. -/
theorem freePathProfile_le_phys
    (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U)
    (cert : PathwisePhysicalCertificate W g μ P)
    {H K : CompactStage t} (a : H ⟶ K) :
    freePathProfile P H K ≤ ObservationSystem.Phys W g μ a := by
  refine iSup_le fun p ↦ ?_
  exact pathTensor_le_phys_arrow W g μ P cert a p

end PhysicalTransfer

end Erdos289
