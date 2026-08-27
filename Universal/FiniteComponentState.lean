import Universal.ReflexiveGraph

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.PNat.Notation

/-!
# Finite component states

Finite induced vertex subobjects of a reflexive graph, with every connected
component labelled by its allowed positive cardinality. Component profiles
take values in Mathlib's free additive commutative monoid `Θ →₀ ℕ`.
-/

open scoped BigOperators

namespace Erdos289

set_option linter.style.haveILetI false

universe u v

/-- The graph induced on a vertex subset. -/
def inducedGraph (G : Graphᵣ.{u}) (S : Set G) : Graphᵣ.{u} where
  carrier := S
  Rel x y := G.Rel x.1 y.1
  refl x := G.refl x.1
  symm h := G.symm h

/-- The vertices in one connected component of an induced graph. -/
abbrev ComponentFiber (G : Graphᵣ.{u}) (S : Set G)
    (c : PiZeroObj (inducedGraph G S)) :=
  {x : inducedGraph G S // piZeroMk (inducedGraph G S) x = c}

/-- The positive cardinality of an induced connected component. -/
noncomputable def componentCardinality (G : Graphᵣ.{u}) (S : Set G)
    (hS : S.Finite) (c : PiZeroObj (inducedGraph G S)) : ℕ+ := by
  letI : Finite (inducedGraph G S).carrier := hS
  letI : Finite (ComponentFiber G S c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ComponentFiber G S c) := Fintype.ofFinite _
  refine ⟨Fintype.card (ComponentFiber G S c), Fintype.card_pos_iff.mpr ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  exact ⟨⟨x, rfl⟩⟩

/-- A finite induced vertex subobject whose component sizes belong to `Θ`. -/
structure FiniteComponentState (G : Graphᵣ.{u}) (Θ : Set ℕ+) where
  /-- The finite vertex support. -/
  support : Set G
  /-- Finiteness of the support. -/
  support_finite : support.Finite
  /-- Every induced component has an allowed positive cardinality. -/
  admissible : ∀ c : PiZeroObj (inducedGraph G support),
    componentCardinality G support support_finite c ∈ Θ

@[ext]
theorem FiniteComponentState.ext {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    {S T : FiniteComponentState G Θ} (h : S.support = T.support) : S = T := by
  cases S
  cases T
  cases h
  rfl

namespace FiniteComponentState

variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}

/-- The induced graph carried by a state. -/
abbrev graph (S : FiniteComponentState G Θ) := inducedGraph G S.support

/-- The finite type of connected components of a state. -/
abbrev Components (S : FiniteComponentState G Θ) := PiZeroObj S.graph

/-- A component, labelled by its allowed cardinality type. -/
noncomputable def componentType (S : FiniteComponentState G Θ) (c : S.Components) : Θ :=
  ⟨componentCardinality G S.support S.support_finite c, S.admissible c⟩

instance (S : FiniteComponentState G Θ) : Finite S.Components := by
  letI : Finite S.graph.carrier := S.support_finite
  exact Finite.of_surjective (piZeroMk S.graph) fun c ↦ by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    exact ⟨x, rfl⟩

end FiniteComponentState

/-- The free additive commutative monoid on the allowed component types. -/
abbrev FCM (Θ : Type u) := Θ →₀ ℕ

/-- The multiset-valued fold of the cardinality labels of all components. -/
noncomputable def componentProfile {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    (S : FiniteComponentState G Θ) : FCM Θ := by
  classical
  letI : Fintype S.Components := Fintype.ofFinite _
  exact ∑ c : S.Components, Finsupp.single (S.componentType c) 1

/-- The canonical extension of a label map from the free commutative monoid. -/
noncomputable def componentLabelLift {Θ : Type u} {L : Type v} [AddCommMonoid L]
    (ell : Θ → L) : FCM Θ →+ L :=
  Finsupp.liftAddHom fun θ ↦ (multiplesHom L) (ell θ)

@[simp]
theorem componentLabelLift_single {Θ : Type u} {L : Type v} [AddCommMonoid L]
    (ell : Θ → L) (θ : Θ) :
    componentLabelLift ell (Finsupp.single θ 1) = ell θ := by
  rw [componentLabelLift, Finsupp.liftAddHom_apply_single, multiplesHom_apply, one_nsmul]

/-- The free-commutative-monoid universal property of component labels. -/
theorem componentLabelLift_existsUnique {Θ : Type u} {L : Type v} [AddCommMonoid L]
    (ell : Θ → L) :
    ∃! lift : FCM Θ →+ L,
      ∀ θ, lift (Finsupp.single θ 1) = ell θ := by
  refine ⟨componentLabelLift ell, componentLabelLift_single ell, ?_⟩
  intro lift hlift
  apply Finsupp.liftAddHom.symm.injective
  ext θ
  rw [Finsupp.liftAddHom_symm_apply_apply, Finsupp.liftAddHom_symm_apply_apply,
    hlift, componentLabelLift_single]

/-- An observable is component-local with label map `ell` when it is the fold
of `ell` over the connected components. -/
def IsComponentLocal {G : Graphᵣ.{u}} {Θ : Set ℕ+} {L : Type v} [AddCommMonoid L]
    (ell : Θ → L) (obs : FiniteComponentState G Θ → L) : Prop :=
  ∀ S, obs S = componentLabelLift ell (componentProfile S)

/-- Every component-local additive observable factors through the component
profile, uniquely among maps extending its component label map. -/
theorem componentProfile_universal {G : Graphᵣ.{u}} {Θ : Set ℕ+}
    {L : Type v} [AddCommMonoid L] (ell : Θ → L)
    (obs : FiniteComponentState G Θ → L) (hobs : IsComponentLocal ell obs) :
    ∃! lift : FCM Θ →+ L,
      (∀ θ, lift (Finsupp.single θ 1) = ell θ) ∧
      ∀ S, lift (componentProfile S) = obs S := by
  refine ⟨componentLabelLift ell, ⟨componentLabelLift_single ell, fun S ↦ (hobs S).symm⟩, ?_⟩
  intro lift hlift
  exact (componentLabelLift_existsUnique ell).unique hlift.1 (componentLabelLift_single ell)

end Erdos289
