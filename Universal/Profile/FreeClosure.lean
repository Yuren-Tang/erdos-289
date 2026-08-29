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

/-- Local bookkeeping: append one further correction to the end of a
compact-stage correction string.  Not part of any owned public interface; it
only converts the right-recursive structure of a `Quiver.Path` into the
string built by `CorrectionString.cons`. -/
@[reducible]
private noncomputable def stringSnoc :
    ∀ {H K L : CompactStage t},
      (compactProfileObservationSystem t).CorrectionString M H K →
      (compactProfileObservationSystem t).Correction M K L →
      (compactProfileObservationSystem t).CorrectionString M H L
  | _, _, _, .nil H, e => .cons e (.nil _)
  | _, _, _, .cons head tail, e => .cons head (stringSnoc tail e)

private theorem stringSnoc_composite {H K L : CompactStage t}
    (s : (compactProfileObservationSystem t).CorrectionString M H K)
    (e : (compactProfileObservationSystem t).Correction M K L) :
    (stringSnoc s e).composite = s.composite.comp e := by
  induction s with
  | nil H => simp [ObservationSystem.CorrectionString.composite]
  | cons head tail ih =>
      simp only [ObservationSystem.CorrectionString.composite, ih,
        ObservationSystem.Correction.comp_assoc]

/-- Local bookkeeping: the two zero-grade corrections attached to composable
compact-stage arrows compose to the zero-grade correction of their sum. -/
private theorem profileZeroSection_comp {H K L : CompactStage t}
    (a : H ⟶ K) (b : K ⟶ L) (m₁ m₂ : M) :
    (ObservationSystem.profileZeroSection (t := t) a m₁).comp
        (ObservationSystem.profileZeroSection (t := t) b m₂) =
      ObservationSystem.profileZeroSection (t := t) (a ≫ b) (m₁ + m₂) := by
  apply ObservationSystem.Correction.ext
  · rfl
  · simp [ObservationSystem.Correction.comp, ObservationSystem.profileZeroSection]

/-- Local bookkeeping: the data attached to a single position of a
compact-stage correction string -- a physical family, its finiteness, a
cover of the position's correction, and a branchwise resource bound. -/
private structure PositionData {H K : CompactStage t}
    (correction : (compactProfileObservationSystem t).Correction M H K) where
  family : PhysicalFamily.{u, u} (FiniteComponentState G Θ)
  finite : Finite family.left
  cover : (compactProfileObservationSystem t).Covers M W g family correction
  bound : U
  resource_bound : ∀ b, μ (family.hom b) ≤ bound

/-- Local bookkeeping: position data attached to a `stringSnoc`, built from
the position data of the original string together with the position data of
the newly appended correction. -/
private noncomputable def snocPositionData :
    ∀ {H K L : CompactStage t}
      (s : (compactProfileObservationSystem t).CorrectionString M H K)
      (ps : ∀ a : s.Index, PositionData W g μ (s.arrow a).correction)
      (c : (compactProfileObservationSystem t).Correction M K L)
      (pc : PositionData W g μ c),
      ∀ a : (stringSnoc s c).Index,
        PositionData W g μ ((stringSnoc s c).arrow a).correction := by
  intro H K L s
  induction s with
  | nil H =>
      intro ps c pc a
      simp only [stringSnoc] at a
      rcases a with a | a
      · exact pc
      · exact nomatch a.down
  | cons head tail ih =>
      intro ps c pc a
      simp only [stringSnoc] at a
      rcases a with a | a
      · exact ps (.inl (ULift.up Unit.unit))
      · exact ih (fun a ↦ ps (.inr a)) c pc a

private theorem sum_snocPositionData_bound :
    ∀ {H K L : CompactStage t}
      (s : (compactProfileObservationSystem t).CorrectionString M H K)
      (ps : ∀ a : s.Index, PositionData W g μ (s.arrow a).correction)
      (c : (compactProfileObservationSystem t).Correction M K L)
      (pc : PositionData W g μ c),
      (∑ a, (snocPositionData W g μ s ps c pc a).bound) =
        (∑ a, (ps a).bound) + pc.bound := by
  intro H K L s
  induction s with
  | nil H =>
      intro ps c pc
      rw [Fintype.sum_sum_type]
      have h1 : ∀ a : ULift.{u} Unit,
          (snocPositionData W g μ (ObservationSystem.CorrectionString.nil H) ps c pc
            (Sum.inl a)).bound = pc.bound := fun _ ↦ rfl
      simp [h1]
  | cons head tail ih =>
      intro ps c pc
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      simp only [Fintype.sum_unique]
      have h1 : (snocPositionData W g μ (.cons head tail) ps c pc
          (Sum.inl (ULift.up Unit.unit))).bound =
            (ps (Sum.inl (ULift.up Unit.unit))).bound := rfl
      have h2 : ∀ a, (snocPositionData W g μ (.cons head tail) ps c pc (Sum.inr a)).bound =
          (snocPositionData W g μ tail (fun a ↦ ps (.inr a)) c pc a).bound := fun _ ↦ rfl
      simp only [h1, h2]
      rw [ih (fun a ↦ ps (.inr a)) c pc, add_assoc]

-- The edge-profile assignment against which a path's edge labels are drawn,
-- scoped to this section only.  Declared as a section variable -- rather
-- than an explicit parameter of `PathLabelTuple` below -- because Lean
-- 4.33.0's inductive-family positivity checker rejects an explicit
-- dependent-function-typed parameter whose type mentions the same index
-- types as the family itself, even when that parameter is otherwise
-- unused; auto-inclusion produces the identical signature
-- (`PathLabelTuple P p r`) without tripping the check.  The section keeps
-- this auto-inclusion from reaching the later declarations below, which
-- take `P` as an ordinary explicit parameter instead.
section PathLabelTupleInductive

variable (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U)

/-- The raw tuple of edge labels along a path: at every position, a label
literally drawn from the edge's own profile `P e`, summing -- by the same
recursion defining `pathRawLabels` -- to the specified aggregate label.  No
physical content is attached here: this is purely the combinatorial datum
that `pathRawLabels P p` is the Set-image shadow of
(`PathLabelTuple.mem_pathRawLabels_iff` below), so a `PathwisePhysicalCertificate`
can be required to answer every actual tuple rather than merely some
tuple realizing a given aggregate label. -/
inductive PathLabelTuple :
    ∀ {H K : CompactStage t}, Quiver.Path H K →
      GradeResourceLabel M U → Type (max u v w)
  | nil (H : CompactStage t) :
      PathLabelTuple (Quiver.Path.nil : Quiver.Path H H) 0
  | cons {H K L : CompactStage t} {p : Quiver.Path H K} (e : K ⟶ L)
      (m_e : M) (u_e : U)
      (mem : (m_e, u_e) ∈ (P e : Set (GradeResourceLabel M U)))
      {r' : GradeResourceLabel M U} (tail : PathLabelTuple p r') :
      PathLabelTuple (Quiver.Path.cons p e) (r' + (m_e, u_e))

end PathLabelTupleInductive

namespace PathLabelTuple

variable {P}

/-- Every raw tuple is a literal decomposition of a member of
`pathRawLabels`. -/
theorem mem_pathRawLabels {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r) :
    r ∈ pathRawLabels P p := by
  induction d with
  | nil => simp [pathRawLabels]
  | cons e m_e u_e mem tail ih =>
      simp only [pathRawLabels]
      exact Set.add_mem_add ih mem

/-- Conversely, every member of `pathRawLabels` is witnessed by some raw
tuple: together with `mem_pathRawLabels`, this exhibits `pathRawLabels P p`
as exactly the Set-image shadow of the Type-valued `PathLabelTuple` data. -/
theorem nonempty_of_mem_pathRawLabels :
    ∀ {H K : CompactStage t} (p : Quiver.Path H K) {r : GradeResourceLabel M U},
      r ∈ pathRawLabels P p → Nonempty (PathLabelTuple P p r)
  | _, _, .nil, r, hr => by
      simp only [pathRawLabels, Set.mem_singleton_iff] at hr
      subst hr
      exact ⟨.nil _⟩
  | _, _, .cons p e, r, hr => by
      simp only [pathRawLabels] at hr
      obtain ⟨r', hr', ⟨m_e, u_e⟩, hre, rfl⟩ := hr
      obtain ⟨d'⟩ := nonempty_of_mem_pathRawLabels p hr'
      exact ⟨.cons e m_e u_e hre d'⟩

theorem mem_pathRawLabels_iff {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} :
    r ∈ pathRawLabels P p ↔ Nonempty (PathLabelTuple P p r) :=
  ⟨nonempty_of_mem_pathRawLabels p, fun ⟨d⟩ ↦ d.mem_pathRawLabels⟩

end PathLabelTuple

/-- Local bookkeeping: the correction string and position data of an
edge-label witness tuple, built together so that the string and the
positions it indexes stay definitionally in lockstep; the composite-label
and resource-total identities are proved alongside the construction itself
so no later proof needs to re-unfold the recursive builder. -/
private structure BuiltEdges {H K : CompactStage t} (p : Quiver.Path H K)
    (r : GradeResourceLabel M U) where
  string : (compactProfileObservationSystem t).CorrectionString M H K
  positions : ∀ a : string.Index, PositionData W g μ (string.arrow a).correction
  composite_eq : string.composite =
    ObservationSystem.profileZeroSection (t := t) (CategoryTheory.composePath p) r.1
  sum_bound_eq : (∑ a, (positions a).bound) = r.2

-- `P` is made implicit here (unlike the outer explicit `W g μ`) because
-- every later use supplies it only via an explicit `PathLabelTuple P p r`
-- argument, from whose type it is always inferable; `W`, `g`, `μ` do not
-- appear in that argument's type, so they stay explicit throughout (as
-- elsewhere in this file) and are always supplied by name.
variable {P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U}

/-- The physical witness data attached to one specific raw tuple: at every
position of `d`, a `PhysWitness` for that very position's label -- the same
`(m_e, u_e)` fixed by `d` itself, not an independently chosen one.  This is
the pathwise counterpart of `PhysWitness`, indexed by the exact tuple it
realizes. -/
noncomputable def PathwisePhysics :
    ∀ {H K : CompactStage t} {p : Quiver.Path H K} {r : GradeResourceLabel M U},
      PathLabelTuple P p r → Type (max (u + 1) v w)
  | _, _, _, _, .nil H => PUnit
  | _, _, _, _, .cons e m_e u_e _mem tail =>
      ObservationSystem.PhysWitness W g μ e m_e u_e × PathwisePhysics tail

private noncomputable def PathLabelTuple.build :
    ∀ {H K : CompactStage t} {p : Quiver.Path H K} {r : GradeResourceLabel M U}
      (d : PathLabelTuple P p r), PathwisePhysics W g μ d → BuiltEdges W g μ p r := by
  intro H K p r d
  induction d with
  | nil =>
      intro _
      refine {
        string := .nil H
        positions := fun (x : ULift.{u} Empty) ↦ nomatch x.down
        composite_eq := ?_
        sum_bound_eq := ?_ }
      · apply ObservationSystem.Correction.ext
        · rfl
        · rfl
      · simp
  | cons e m_e u_e _mem tail ih =>
      intro phys
      simp only [PathwisePhysics] at phys
      obtain ⟨witness, physTail⟩ := phys
      let btail := ih physTail
      let pc : PositionData W g μ (ObservationSystem.profileZeroSection (t := t) e m_e) :=
        { family := witness.family.family,
          finite := witness.family.finite_domain,
          cover := witness.cover,
          bound := u_e,
          resource_bound := witness.resource_bound }
      refine {
        string := stringSnoc btail.string
          (ObservationSystem.profileZeroSection (t := t) e m_e)
        positions := snocPositionData W g μ btail.string btail.positions
          (ObservationSystem.profileZeroSection (t := t) e m_e) pc
        composite_eq := ?_
        sum_bound_eq := ?_ }
      · rw [stringSnoc_composite, btail.composite_eq, profileZeroSection_comp,
          CategoryTheory.composePath_cons]
        rfl
      · rw [sum_snocPositionData_bound, btail.sum_bound_eq]
        rfl

namespace PathLabelTuple

/-- The canonical correction string of a raw tuple's physical realization:
each position carries the simple zero correction at its local grade. -/
noncomputable def toString {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) :
    (compactProfileObservationSystem t).CorrectionString M H K :=
  (build W g μ d phys).string

/-- The canonical position data of a raw tuple's physical realization: at
each position, the local witness's own family, cover, and resource
bound. -/
noncomputable def toPositionData {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) :
    ∀ a : (toString W g μ d phys).Index,
      PositionData W g μ ((toString W g μ d phys).arrow a).correction :=
  (build W g μ d phys).positions

/-- The canonical local families of a raw tuple's physical realization. -/
noncomputable def toFamilies {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) :
    ∀ _a : (toString W g μ d phys).Index,
      PhysicalFamily.{u, u} (FiniteComponentState G Θ) :=
  fun a ↦ (toPositionData W g μ d phys a).family

instance instFiniteToFamilies {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) (a : (toString W g μ d phys).Index) :
    Finite (toFamilies W g μ d phys a).left :=
  (toPositionData W g μ d phys a).finite

theorem toString_composite {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) :
    (toString W g μ d phys).composite =
      ObservationSystem.profileZeroSection (t := t)
        (CategoryTheory.composePath p) r.1 :=
  (build W g μ d phys).composite_eq

theorem sum_toPositionData_bound {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) :
    (∑ a, (toPositionData W g μ d phys a).bound) = r.2 :=
  (build W g μ d phys).sum_bound_eq

theorem local_cover {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) (a : (toString W g μ d phys).Index) :
    (compactProfileObservationSystem t).Covers M W g
      (toFamilies W g μ d phys a) ((toString W g μ d phys).arrow a).correction :=
  (toPositionData W g μ d phys a).cover

theorem local_resource_bound {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r)
    (phys : PathwisePhysics W g μ d) (a : (toString W g μ d phys).Index)
    (b : (toFamilies W g μ d phys a).left) :
    μ ((toFamilies W g μ d phys a).hom b) ≤ (toPositionData W g μ d phys a).bound :=
  (toPositionData W g μ d phys a).resource_bound b

end PathLabelTuple

/-- A pathwise physical-composition certificate at a literal edge-label
tuple.  The tuple carries, for every edge, a label drawn from that edge's
own profile together with the local `PhysWitness` realizing that same
label; the correction string, local families, local covers, resource
bounds, and composite zero correction are all canonically derived from this
same tuple.  The only further datum is the regular-epimorphism certificate
for the resulting compatible-realizer map, matching the specification's
regular-epimorphic physical composition certificate for every tuple of edge
labels (U7.7). -/
structure PathwiseCompositionData
    (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U)
    {H K : CompactStage t} {p : Quiver.Path H K} {r : GradeResourceLabel M U}
    (d : PathLabelTuple P p r) where
  phys : PathwisePhysics W g μ d
  compatible_regularEpi : TypeRegularEpi
    (ObservationSystem.compatibleRealizerMap
      (O := compactProfileObservationSystem t) (M := M) (W := W) (g := g)
      (PathLabelTuple.toString W g μ d phys) (PathLabelTuple.toFamilies W g μ d phys))

/-- A pathwise physical-composition certificate.  For every actual raw
tuple of edge labels -- not merely for some tuple realizing a given
aggregate label -- it supplies edge-local realizers matching that exact
tuple and the regular-epimorphic compatible-realizer comparison required by
the frozen composition spine. -/
structure PathwisePhysicalCertificate
    (P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U) where
  realize : ∀ {H K : CompactStage t} {p : Quiver.Path H K}
    {r : GradeResourceLabel M U} (d : PathLabelTuple P p r),
      Nonempty (PathwiseCompositionData W g μ P d)

/-- The frozen regular-epimorphic n-ary composition criterion turns the
pathwise edge-local data into the composite physical witness realizing the
tuple's own aggregate label. -/
noncomputable def PathwiseCompositionData.toPhysWitness
    {P : ∀ {H K : CompactStage t}, (H ⟶ K) → BoundProfile M U}
    {H K : CompactStage t} {p : Quiver.Path H K} {r : GradeResourceLabel M U}
    {d : PathLabelTuple P p r} (c : PathwiseCompositionData W g μ P d) :
    ObservationSystem.PhysWitness W g μ
      (CategoryTheory.composePath p) r.1 r.2 := by
  let O := compactProfileObservationSystem t
  let F := ObservationSystem.compatibleRealizerSumFamily
    (O := O) (M := M) (W := W) (g := g)
    (PathLabelTuple.toString W g μ d c.phys) (PathLabelTuple.toFamilies W g μ d c.phys)
  haveI : Finite F.left := ObservationSystem.instFiniteCompatibleRealizer
    (O := O) (M := M) (W := W) (g := g)
    (PathLabelTuple.toString W g μ d c.phys) (PathLabelTuple.toFamilies W g μ d c.phys)
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
  · have hcover : O.Covers M W g F
        (PathLabelTuple.toString W g μ d c.phys).composite :=
      (ObservationSystem.naryCompositionCriterion_regularEpi
      (O := O) (M := M) (W := W) (g := g)
      (PathLabelTuple.toString W g μ d c.phys)
      (PathLabelTuple.toFamilies W g μ d c.phys)).2 c.compatible_regularEpi
    rw [PathLabelTuple.toString_composite W g μ d c.phys] at hcover
    change O.Covers M W g Fsmall
      (ObservationSystem.profileZeroSection (t := t)
        (CategoryTheory.composePath p) r.1)
    intro target
    obtain ⟨r', hr⟩ := hcover target
    refine ⟨{
      left := ULift.up (e r'.branch)
      right := r'.universal
      condition := ?_ }, hr⟩
    change F.hom (e.symm (e r'.branch)) = r'.universal.state
    rw [e.symm_apply_apply]
    exact r'.family_state_eq
  · intro n
    let b := e.symm n.down
    calc
      μ (Fsmall.hom n) = ∑ a, μ ((b.1 a).universal.state) := by
        exact μ.map_finitePhysicalUnion
          (⟨fun a ↦ (b.1 a).universal.state, b.2⟩ :
            NaryPhysicalDomain G Θ (PathLabelTuple.toString W g μ d c.phys).Index)
      _ = ∑ a, μ ((PathLabelTuple.toFamilies W g μ d c.phys a).hom ((b.1 a).branch)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [(b.1 a).family_state_eq]
      _ ≤ ∑ a, (PathLabelTuple.toPositionData W g μ d c.phys a).bound := by
        exact Finset.sum_le_sum fun a _ ↦
          PathLabelTuple.local_resource_bound W g μ d c.phys a ((b.1 a).branch)
      _ = r.2 := PathLabelTuple.sum_toPositionData_bound W g μ d c.phys

/-- Each certified path tensor is contained in physical realization.  A
raw label is first turned into an actual tuple of edge labels drawn from
the profiles, and the certificate is then applied to that exact tuple. -/
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
    obtain ⟨d⟩ := PathLabelTuple.nonempty_of_mem_pathRawLabels p hraw
    rcases cert.realize d with ⟨c⟩
    exact ⟨c.toPhysWitness⟩

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
