import Universal.Target.CompactResolution
import Universal.Correction.Realizer
import Universal.Correction.Core

/-!
# Exact transfer for an arbitrary marking

This module uses the compact quotient resolution as the observation system.
The exact marked fibre is the literal pullback `C ×_Γ T`; the target
realizer is the literal pullback of a family realizer along the distinguished
zero source requirement.
-/

open CategoryTheory
open QuotientAddGroup

namespace Erdos289

universe u v w

/-- The compact quotient resolution, viewed as the commutative-monoid-valued
observation system used by the correction spine. -/
def compactResolutionObservationSystem
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

variable {Γ : Type u} [AddCommGroup Γ]
variable {t : Marking Γ}
variable {M : Type v} [AddCommMonoid M]
variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}
variable (W : PhysicalAdditiveMap G Θ Γ)
variable (g : PhysicalAdditiveMap G Θ M)

private abbrev compactO := compactResolutionObservationSystem t

/-- The zero correction `s₀(u,m) = (u;(0,m))`. -/
def zeroSection {H K : CompactStage t} (u : H ⟶ K) (m : M) :
    compactO.Correction M H K where
  base := u
  label := (0, m)

/-- The distinguished source requirement `(0,m)` of a zero correction. -/
def zeroRequired {H K : CompactStage t} (u : H ⟶ K) (m : M) :
    compactO.Required M (zeroSection u m) :=
  ⟨(0, m), by
    apply Prod.ext <;> simp [zeroSection]⟩

/-- The exact marked fibre `C_t = C ×_Γ T`. -/
def ExactMarkedFiber :=
  TypePullback W t.hom

namespace ExactMarkedFiber

/-- Physical state underlying a point of the exact marked fibre. -/
def state (x : ExactMarkedFiber (t := t) W) : FiniteComponentState G Θ :=
  x.left

/-- Mark witnessing the exact target value. -/
def mark (x : ExactMarkedFiber (t := t) W) : t.left :=
  x.right

@[simp]
theorem value_eq_mark (x : ExactMarkedFiber (t := t) W) :
    W x.state = t.hom x.mark :=
  x.condition

end ExactMarkedFiber

/-- The exact grade spectrum of a marking. -/
def ExactSpectrum : Set M :=
  {m | ∃ x : ExactMarkedFiber (t := t) W, g x.state = m}

/-- A marking morphism induces the canonical map of exact marked fibres. -/
def exactMarkedFiber_map {t' : Marking Γ} (h : t ⟶ t') :
    ExactMarkedFiber (t := t) W → ExactMarkedFiber (t := t') W :=
  fun x ↦
    { left := x.left
      right := h.left x.right
      condition := by
        rw [x.condition]
        exact (CategoryTheory.congr_fun (Over.w h) x.right).symm }

/-- Identity coherence of the exact-marked-fibre comparison. -/
theorem exactMarkedFiber_map_id :
    exactMarkedFiber_map (t := t) W (𝟙 t) = id := by
  funext x
  apply TypePullback.ext <;> rfl

/-- Composition coherence of the exact-marked-fibre comparison. -/
theorem exactMarkedFiber_map_comp {t' t'' : Marking Γ}
    (h : t ⟶ t') (k : t' ⟶ t'') :
    exactMarkedFiber_map W (h ≫ k) =
      exactMarkedFiber_map W k ∘ exactMarkedFiber_map W h := by
  funext x
  apply TypePullback.ext <;> rfl

/-- Exact spectra are monotone under morphisms of markings. -/
theorem exactSpectrum_mono_marking {t' : Marking Γ} (h : t ⟶ t') :
    ExactSpectrum (t := t) W g ⊆ ExactSpectrum (t := t') W g := by
  rintro m ⟨x, hx⟩
  exact ⟨exactMarkedFiber_map W h x, hx⟩

/-- Pullback of the family realizer along the distinguished zero source
requirement. -/
def TargetRealizer {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (u : H ⟶ K) (m : M) :=
  TypePullback (fun _ : Unit ↦ zeroRequired u m)
    (FamilyRealizer.required :
      compactO.FamilyRealizer M W g F (zeroSection u m) →
        compactO.Required M (zeroSection u m))

namespace TargetRealizer

/-- Family realizer underlying a target realizer. -/
def family {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (r : TargetRealizer W g F u m) :
    compactO.FamilyRealizer M W g F (zeroSection u m) :=
  r.right

/-- Physical state underlying a target realizer. -/
def state {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (r : TargetRealizer W g F u m) : FiniteComponentState G Θ :=
  r.family.universal.state

/-- Pullback stability of regular epimorphisms in the fixed `Type` setting:
a zero-correction cover makes the target-realizer projection surjective. -/
theorem projection_surjective {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ)) (u : H ⟶ K) (m : M)
    (hcover : compactO.Covers M W g F (zeroSection u m)) :
    Function.Surjective
      (TypePullback.fst : TargetRealizer W g F u m → Unit) :=
  TypePullback.fst_surjective_of_right_surjective hcover

end TargetRealizer

/-- A target realizer factors through the exact marked fibre without changing
its physical-state coordinate. -/
def TargetRealizerFactorsThroughExactFiber {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (u : H ⟶ K) (m : M) : Prop :=
  ∃ lift : TargetRealizer W g F u m → ExactMarkedFiber (t := t) W,
    ∀ r, ExactMarkedFiber.state W (lift r) =
      TargetRealizer.state W g r

/-- Frozen exact-transfer theorem: a zero-correction cover whose target
realizer factors through `C_t` realizes the required exact grade. -/
theorem exactTransfer {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (u : H ⟶ K) (m : M)
    (hcover : compactO.Covers M W g F (zeroSection u m))
    (hfactor : TargetRealizerFactorsThroughExactFiber W g F u m) :
    m ∈ ExactSpectrum (t := t) W g := by
  obtain ⟨fr, hfr⟩ := hcover (zeroRequired u m)
  let r : TargetRealizer W g F u m :=
    ⟨(), fr, hfr.symm⟩
  obtain ⟨lift, hlift⟩ := hfactor
  refine ⟨lift r, ?_⟩
  rw [hlift r]
  have hobs := congrArg Prod.snd fr.universal.observation_eq
  have hreq := congrArg (fun q ↦ q.val.2) hfr
  exact hobs.trans hreq

/-- Exact transfer is natural under a morphism of markings: applying the
arbitrary-marking theorem and then the canonical exact-fibre map realizes the
same grade for the target marking. -/
theorem exactTransfer_natural_marking {t' : Marking Γ} (h : t ⟶ t')
    {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (u : H ⟶ K) (m : M)
    (hcover : compactO.Covers M W g F (zeroSection u m))
    (hfactor : TargetRealizerFactorsThroughExactFiber W g F u m) :
    m ∈ ExactSpectrum (t := t') W g :=
  exactSpectrum_mono_marking W g h
    (exactTransfer W g F u m hcover hfactor)

/-- Singleton-target specialization of exact transfer. -/
theorem exactTransfer_singleton {τ : Γ}
    {H K : CompactStage (singletonMarking τ)}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (u : H ⟶ K) (m : M)
    (hcover : (compactResolutionObservationSystem (singletonMarking τ)).Covers
      M W g F (zeroSection u m))
    (hfactor : TargetRealizerFactorsThroughExactFiber
      (t := singletonMarking τ) W g F u m) :
    m ∈ ExactSpectrum (t := singletonMarking τ) W g :=
  exactTransfer W g F u m hcover hfactor

end ObservationSystem

end Erdos289
