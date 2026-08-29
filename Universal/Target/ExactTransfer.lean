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

/-- The graded quotient comparison induced by a marking morphism at a compact
stage; it changes only the compact-quotient coordinate. -/
def compactGraded_mapMarking {t' : Marking Γ} (h : t ⟶ t')
    (H : CompactStage t) :
    ((CenteredMarking t ⧸ H.1) × M) →
      ((CenteredMarking t' ⧸ ((compactStage_mapMarking h).obj H).1) × M) :=
  fun x ↦ ((compactResolution_mapMarking h).app H x.1, x.2)

/-- Compact quotient comparison commutes with the physical observation. -/
theorem compactPhysicalObservation_mapMarking {t' : Marking Γ} (h : t ⟶ t')
    (H : CompactStage t) (c : FiniteComponentState G Θ) :
    compactGraded_mapMarking (M := M) h H
        (compactO.physicalObservation M W g H c) =
      (compactResolutionObservationSystem t').physicalObservation M W g
        ((compactStage_mapMarking h).obj H) c := by
  apply Prod.ext
  · rfl
  · rfl

/-- Identity coherence of the graded quotient comparison, with the canonical
stage transport supplied by U4.3. -/
theorem compactGraded_mapMarking_id (H : CompactStage t)
    (x : (CenteredMarking t ⧸ H.1) × M) :
    ((compactResolution t).map
        ((compactStage_mapMarking_idIso (t := t)).hom.app H)
        (compactGraded_mapMarking (M := M) (𝟙 t) H x).1,
      (compactGraded_mapMarking (M := M) (𝟙 t) H x).2) = x := by
  apply Prod.ext
  · have hnat := congrArg (fun η ↦ η.app H)
      (compactResolution_mapMarking_id (t := t))
    exact ConcreteCategory.congr_hom hnat x.1
  · rfl

/-- Composition coherence of the graded quotient comparison, with the
canonical stage transport supplied by U4.3. -/
theorem compactGraded_mapMarking_comp {t' t'' : Marking Γ}
    (h : t ⟶ t') (k : t' ⟶ t'') (H : CompactStage t)
    (x : (CenteredMarking t ⧸ H.1) × M) :
    ((compactResolution t'').map
        ((compactStage_mapMarking_compIso h k).hom.app H)
        (compactGraded_mapMarking (M := M) (h ≫ k) H x).1,
      (compactGraded_mapMarking (M := M) (h ≫ k) H x).2) =
      compactGraded_mapMarking (M := M) k ((compactStage_mapMarking h).obj H)
        (compactGraded_mapMarking (M := M) h H x) := by
  apply Prod.ext
  · have hnat := congrArg (fun η ↦ η.app H)
      (compactResolution_mapMarking_comp h k)
    exact ConcreteCategory.congr_hom hnat x.1
  · rfl

/-- The quotient comparison maps requirements of a zero correction to
requirements of the corresponding zero correction. -/
def zeroRequired_mapMarking {t' : Marking Γ} (h : t ⟶ t')
    {H K : CompactStage t} (u : H ⟶ K) (m : M) :
    compactO.Required M (zeroSection u m) →
      (compactResolutionObservationSystem t').Required M
        (zeroSection ((compactStage_mapMarking h).map u) m) := by
  intro x
  refine ⟨compactGraded_mapMarking (M := M) h H x.1, ?_⟩
  apply Prod.ext
  · have hx := congrArg Prod.fst x.2
    change (compactResolution t).map u x.1.1 = 0 at hx
    change (compactResolution t').map ((compactStage_mapMarking h).map u)
      ((compactResolution_mapMarking h).app H x.1.1) = 0
    calc
      _ = (compactResolution_mapMarking h).app K
          ((compactResolution t).map u x.1.1) := by
            exact (ConcreteCategory.congr_hom
              ((compactResolution_mapMarking h).naturality u) x.1.1).symm
      _ = 0 := by rw [hx]; exact map_zero _
  · have hx := congrArg Prod.snd x.2
    change x.1.2 = m at hx
    exact hx

/-- The distinguished zero source requirement is preserved by comparison. -/
theorem zeroRequired_mapMarking_zero {t' : Marking Γ} (h : t ⟶ t')
    {H K : CompactStage t} (u : H ⟶ K) (m : M) :
    zeroRequired_mapMarking (M := M) h u m (zeroRequired u m) =
      zeroRequired ((compactStage_mapMarking h).map u) m := by
  apply Subtype.ext
  apply Prod.ext
  · exact map_zero _
  · rfl

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

/-- Structural comparison of family realizers for zero corrections under a
marking morphism. -/
def family_mapMarking {t' : Marking Γ} (h : t ⟶ t')
    {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M} :
    compactO.FamilyRealizer M W g F (zeroSection u m) →
      (compactResolutionObservationSystem t').FamilyRealizer M W g F
        (zeroSection ((compactStage_mapMarking h).map u) m) := by
  intro r
  let universal :
      (compactResolutionObservationSystem t').UniversalRealizer M W g
        (zeroSection ((compactStage_mapMarking h).map u) m) :=
    ⟨r.universal.state,
      zeroRequired_mapMarking (M := M) h u m r.required, by
        rw [← compactPhysicalObservation_mapMarking (M := M) W g h H]
        exact congrArg (compactGraded_mapMarking (M := M) h H)
          r.universal.condition⟩
  refine ⟨r.branch, universal, ?_⟩
  change F.hom r.branch = r.universal.state
  exact r.condition

/-- Structural comparison of target realizers under a marking morphism. -/
def mapMarking {t' : Marking Γ} (h : t ⟶ t')
    {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M} :
    TargetRealizer W g F u m →
      TargetRealizer (t := t') W g F
        ((compactStage_mapMarking h).map u) m := by
  intro r
  refine ⟨r.left, family_mapMarking W g h r.family, ?_⟩
  rw [← zeroRequired_mapMarking_zero (M := M) h u m]
  exact congrArg (zeroRequired_mapMarking (M := M) h u m) r.condition

/-- Target-realizer comparison preserves the physical state coordinate. -/
@[simp]
theorem state_mapMarking {t' : Marking Γ} (h : t ⟶ t')
    {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (r : TargetRealizer W g F u m) :
    state (t := t') W g (mapMarking W g h r) = state W g r :=
  rfl

/-- Identity coherence on the invariant physical-state coordinate. -/
theorem mapMarking_id_state
    {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (r : TargetRealizer W g F u m) :
    state (t := t) W g (mapMarking W g (𝟙 t) r) = state W g r :=
  state_mapMarking W g (𝟙 t) r

/-- Composition coherence on the invariant physical-state coordinate. -/
theorem mapMarking_comp_state {t' t'' : Marking Γ}
    (h : t ⟶ t') (k : t' ⟶ t'')
    {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (r : TargetRealizer W g F u m) :
    state (t := t'') W g
        (mapMarking W g k (mapMarking W g h r)) = state W g r := by
  rw [state_mapMarking, state_mapMarking]

/-- Direct and iterated marking comparisons agree on the invariant physical
state, while their dependent stage coordinates are identified by U4.3. -/
theorem mapMarking_comp_state_coherence {t' t'' : Marking Γ}
    (h : t ⟶ t') (k : t' ⟶ t'')
    {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (r : TargetRealizer W g F u m) :
    state (t := t'') W g
        (mapMarking W g k (mapMarking W g h r)) =
      state (t := t'') W g (mapMarking W g (h ≫ k) r) := by
  rw [state_mapMarking, state_mapMarking, state_mapMarking]

/-- Pullback stability of regular epimorphisms in the fixed `Type` setting:
a zero-correction cover makes the target-realizer projection surjective. -/
theorem projection_surjective {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ)) (u : H ⟶ K) (m : M)
    (hcover : compactO.Covers M W g F (zeroSection u m)) :
    Function.Surjective
      (TypePullback.fst : TargetRealizer W g F u m → Unit) :=
  TypePullback.fst_surjective_of_right_surjective hcover

/-- Invariant U6.2 formulation in the fixed category `Type`. -/
theorem projection_regularEpi {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ)) (u : H ⟶ K) (m : M)
    (hcover : compactO.Covers M W g F (zeroSection u m)) :
    TypeRegularEpi
      (TypePullback.fst : TargetRealizer W g F u m → Unit) :=
  (type_regularEpi_iff_surjective _).2
    (projection_surjective W g F u m hcover)

end TargetRealizer

/-- A target realizer factors through the exact marked fibre without changing
its physical-state coordinate. -/
def TargetRealizerFactorsThroughExactFiber {H K : CompactStage t}
    (F : PhysicalFamily (FiniteComponentState G Θ))
    (u : H ⟶ K) (m : M) : Prop :=
  ∃ lift : TargetRealizer W g F u m → ExactMarkedFiber (t := t) W,
    ∀ r, ExactMarkedFiber.state W (lift r) =
      TargetRealizer.state W g r

/-- The target-realizer and exact-marked-fibre comparisons commute over their
common physical-state coordinate. -/
theorem targetRealizer_exactMarkedFiber_commutes {t' : Marking Γ}
    (h : t ⟶ t') {H K : CompactStage t}
    {F : PhysicalFamily (FiniteComponentState G Θ)} {u : H ⟶ K} {m : M}
    (lift : TargetRealizer W g F u m → ExactMarkedFiber (t := t) W)
    (hlift : ∀ r, ExactMarkedFiber.state W (lift r) =
      TargetRealizer.state W g r)
    (r : TargetRealizer W g F u m) :
    ExactMarkedFiber.state W (exactMarkedFiber_map W h (lift r)) =
      TargetRealizer.state (t := t') W g
        (TargetRealizer.mapMarking W g h r) := by
  rw [TargetRealizer.state_mapMarking]
  exact hlift r

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
    m ∈ ExactSpectrum (t := t') W g := by
  obtain ⟨fr, hfr⟩ := hcover (zeroRequired u m)
  let r : TargetRealizer W g F u m := ⟨(), fr, hfr.symm⟩
  obtain ⟨lift, hlift⟩ := hfactor
  refine ⟨exactMarkedFiber_map W h (lift r), ?_⟩
  rw [targetRealizer_exactMarkedFiber_commutes W g h lift hlift r]
  rw [TargetRealizer.state_mapMarking]
  have hobs := congrArg Prod.snd fr.universal.observation_eq
  have hreq := congrArg (fun q ↦ q.val.2) hfr
  exact hobs.trans hreq

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
