import AffineCorrection.Physical
import AffineCorrection.GradedCorrection

/-!
# Realizer pullbacks and minimal physical composition

Coverage is the surjectivity of the projection from a literal realizer
pullback to the required correction fibre.

Composition uses only the surjectivity of the canonical map from compatible
realizer pairs to the composite required fibre.  No whole-family
cross-compatibility hypothesis is present.
-/

set_option autoImplicit false

open CategoryTheory

namespace AffineCorrection

universe u v w x y

variable
    {I : Type u} [Category.{w, u} I]
    {Γ : Type v} [AddCommGroup Γ]
    {M : Type y} [AddCommMonoid M]
    (O : ObservationSystem I Γ)

/-- Joint correction-grade observation of a physical state at level `i`. -/
def physicalObservation
    {C : Type x} (W : C → Γ) (g : C → M)
    (i : I) (c : C) : O.Q.obj i × M :=
  (O.observe i (W c), g c)

/--
The literal pullback of a physical subfamily over a required correction fibre.
-/
structure Realizer
    {C : Type x} (W : C → Γ) (g : C → M)
    {X Y : GradedCorrection O M}
    (F : Set C) (f : X ⟶ Y) where
  /-- Physical state in the family. -/
  state : F
  /-- Required graded observation represented by the state. -/
  req : GradedCorrection.Required O M f
  /-- Pullback commutativity. -/
  observation_eq :
    physicalObservation O W g X.level state.1 = req.1

namespace Realizer

variable
    {O}
    {C : Type x} {W : C → Γ} {g : C → M}
    {X Y : GradedCorrection O M}
    {F : Set C} {f : X ⟶ Y}

/-- Projection from the realizer pullback to the required fibre. -/
def toRequired (r : Realizer O W g F f) :
    GradedCorrection.Required O M f :=
  r.req

/-- The realized state has the correction's prescribed grade. -/
theorem grade_eq (r : Realizer O W g F f) :
    g r.state.1 = f.grade := by
  have h₁ := congrArg Prod.snd r.observation_eq
  exact h₁.trans r.req.property.2

/-- The realized exact observation transports to the correction label. -/
theorem transition_observation_eq_label (r : Realizer O W g F f) :
    O.transition f.base (O.observe X.level (W r.state.1)) = f.label := by
  have h₁ := congrArg Prod.fst r.observation_eq
  change O.observe X.level (W r.state.1) = r.req.1.1 at h₁
  rw [h₁]
  exact r.req.property.1

end Realizer

/--
`F` covers `f` iff the realizer pullback projection is surjective.
In `Type`, this is exactly the concrete epi condition.
-/
def Covers
    {C : Type x} (W : C → Γ) (g : C → M)
    {X Y : GradedCorrection O M}
    (F : Set C) (f : X ⟶ Y) : Prop :=
  Function.Surjective (Realizer.toRequired (O := O) (W := W) (g := g) (F := F) (f := f))

/--
Compatible pairs of local realizers together with the actual physical sum they
produce.
-/
structure CompatibleRealizer
    {C : Type x} (P : PartialAddCommMonoid C)
    (W : C → Γ) (g : C → M)
    {X Y Z : GradedCorrection O M}
    (F R : Set C) (f : X ⟶ Y) (r : Y ⟶ Z) where
  /-- Left local realizer. -/
  left : Realizer O W g F f
  /-- Right local realizer. -/
  right : Realizer O W g R r
  /-- Their actual defined physical composite. -/
  sum : C
  /-- Witness that the physical composite is defined. -/
  sum_spec : P.add left.state.1 right.state.1 sum

namespace CompatibleRealizer

variable
    {O}
    {C : Type x}
    {P : PartialAddCommMonoid C}
    {W : C → Γ} {g : C → M}
    {X Y Z : GradedCorrection O M}
    {F R : Set C} {f : X ⟶ Y} {r : Y ⟶ Z}

/--
Canonical map from compatible local realizer pairs to the required fibre of
the composite correction.
-/
def toCompositeRequired
    (hW : IsAdditiveOn P W) (hg : IsAdditiveOn P g)
    (c : CompatibleRealizer O P W g F R f r) :
    GradedCorrection.Required O M (f ≫ r) :=
  ⟨physicalObservation O W g X.level c.sum, by
    constructor
    · change O.transition (f.base ≫ r.base) (O.observe X.level (W c.sum)) =
        O.transition r.base f.label + r.label
      rw [hW c.sum_spec]
      rw [map_add]
      rw [O.transition_comp]
      rw [map_add]
      rw [O.transition_observe f.base (W c.right.state.1)]
      rw [c.left.transition_observation_eq_label]
      rw [map_add]
      rw [c.right.transition_observation_eq_label]
    · change g c.sum = f.grade + r.grade
      rw [hg c.sum_spec]
      rw [c.left.grade_eq, c.right.grade_eq]⟩

end CompatibleRealizer

/--
The exact minimal physical composition hypothesis: the canonical compatible-
realizer map is surjective onto the composite required fibre.
-/
def CompositionCovers
    {C : Type x} (P : PartialAddCommMonoid C)
    (W : C → Γ) (g : C → M)
    {X Y Z : GradedCorrection O M}
    (F R : Set C) (f : X ⟶ Y) (r : Y ⟶ Z)
    (hW : IsAdditiveOn P W) (hg : IsAdditiveOn P g) : Prop :=
  Function.Surjective
    (CompatibleRealizer.toCompositeRequired
      (O := O) (P := P) (W := W) (g := g)
      (F := F) (R := R) (f := f) (r := r) hW hg)

/--
The minimal composition-epi condition implies coverage by the family of actual
physical sums.
-/
theorem covers_comp_of_compositionCovers
    {C : Type x} (P : PartialAddCommMonoid C)
    (W : C → Γ) (g : C → M)
    {X Y Z : GradedCorrection O M}
    (F R : Set C) (f : X ⟶ Y) (r : Y ⟶ Z)
    (hW : IsAdditiveOn P W) (hg : IsAdditiveOn P g)
    (hcomp : CompositionCovers O P W g F R f r hW hg) :
    Covers O W g (P.sumFamily F R) (f ≫ r) := by
  intro t
  rcases hcomp t with ⟨c, hc⟩
  subst t
  refine ⟨{
    state := ⟨c.sum, ?_⟩
    req := CompatibleRealizer.toCompositeRequired
      (O := O) (P := P) (W := W) (g := g)
      (F := F) (R := R) (f := f) (r := r) hW hg c
    observation_eq := rfl
  }, rfl⟩
  exact ⟨c.left.state.1, c.left.state.2,
    c.right.state.1, c.right.state.2, c.sum_spec⟩

end AffineCorrection
