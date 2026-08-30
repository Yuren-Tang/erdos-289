import Universal.FiniteComponentState
import Universal.PhysicalPartialMonoid

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# E289 physical specialization

The reciprocal specialization of the universal finite-component physical system:
the reflexive successor graph on the positive vertex object, the allowed
component object `Θ = {2,3}`, the E289 state object together with its component
profile, grade, and reciprocal value, and the finite physical constraints used
to express remoteness of later constructions from an earlier finite footprint.
-/

open scoped BigOperators NNRat

namespace Erdos289

set_option linter.style.haveILetI false

universe v

/-- Graph distance in the successor graph, `d(m,n) = |m-n|`. -/
def successorDist (m n : ℕ+) : ℕ := ((m : ℕ) - (n : ℕ) : ℤ).natAbs

@[simp]
theorem successorDist_self (m : ℕ+) : successorDist m m = 0 := by
  simp [successorDist]

theorem successorDist_comm (m n : ℕ+) : successorDist m n = successorDist n m := by
  simp only [successorDist]
  omega

/-- The reflexive successor graph `ℙ` on the positive vertex object
`V₊ = ℕ_{>0}`. -/
def successorGraph : Graphᵣ.{0} where
  carrier := ℕ+
  Rel m n := successorDist m n ≤ 1
  refl m := by simp
  symm {m n} h := by rwa [successorDist_comm]

@[simp]
theorem successorGraph_rel (m n : ℕ+) :
    successorGraph.Rel m n ↔ successorDist m n ≤ 1 :=
  Iff.rfl

/-- The allowed component object `Θ = {2,3}`. -/
def allowedComponentTypes : Set ℕ+ := {2, 3}

/-- The E289 state object `C = C_Θ(ℙ)`. -/
abbrev E289State := FiniteComponentState successorGraph allowedComponentTypes

/-- The E289 component-profile monoid `M = FCM(Θ)`. -/
abbrev E289Profile := FCM allowedComponentTypes

/-- The E289 component profile `χ`. -/
noncomputable def stateProfile (S : E289State) : E289Profile :=
  componentProfile S

/-- The augmentation `FCM(Θ) →+ ℕ` counting components. -/
noncomputable def gradeAugmentation : E289Profile →+ ℕ :=
  componentLabelLift fun _ ↦ 1

/-- The E289 grade `g = aug ∘ χ`. -/
noncomputable def grade (S : E289State) : ℕ :=
  gradeAugmentation (stateProfile S)

/-- The reciprocal weight `n ↦ 1/n` on the successor vertex object. -/
def reciprocalWeight (n : ℕ+) : ℚ := 1 / ((n : ℕ) : ℚ)

theorem reciprocalWeight_nonneg (n : ℕ+) : 0 ≤ reciprocalWeight n :=
  div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le (n : ℕ))

/-- The reciprocal value `W(S) = ∑_{n ∈ S} 1/n`. -/
noncomputable def reciprocalValue (S : E289State) : ℚ :=
  vertexFold reciprocalWeight S

/-- The reciprocal value takes values in the nonnegative cone. -/
theorem reciprocalValue_nonneg (S : E289State) : 0 ≤ reciprocalValue S := by
  classical
  letI : Finite S.support := S.support_finite
  letI : Fintype S.support := Fintype.ofFinite _
  unfold reciprocalValue vertexFold
  exact Finset.sum_nonneg fun x _ ↦ reciprocalWeight_nonneg _

/-- The resource corestriction `W₊ : C → ℚ≥0`. -/
noncomputable def reciprocalValuePos (S : E289State) : ℚ≥0 :=
  ⟨reciprocalValue S, reciprocalValue_nonneg S⟩

@[simp]
theorem coe_reciprocalValuePos (S : E289State) :
    ((reciprocalValuePos S : ℚ≥0) : ℚ) = reciprocalValue S :=
  rfl

/-- `W₊` is the unique nonnegative corestriction of `W` along the canonical
inclusion `ℚ≥0 ↪ ℚ`. -/
theorem reciprocalValuePos_unique :
    ∃! f : E289State → ℚ≥0, ∀ S, ((f S : ℚ≥0) : ℚ) = reciprocalValue S := by
  refine ⟨reciprocalValuePos, fun S ↦ rfl, ?_⟩
  intro f hf
  funext S
  exact NNRat.coe_injective (by rw [hf S, coe_reciprocalValuePos])

/-! ## Physical-domain specialization -/

/-- The E289 binary physical domain. -/
abbrev E289BinaryPhysicalDomain :=
  BinaryPhysicalDomain successorGraph allowedComponentTypes

/-- The E289 direct n-ary physical domain. -/
abbrev E289NaryPhysicalDomain (I : Type v) [Fintype I] :=
  NaryPhysicalDomain successorGraph allowedComponentTypes I

/-- The E289 physical partial monoid. -/
noncomputable def e289PhysicalPartialMonoid :
    PhysicalPartialMonoid successorGraph allowedComponentTypes :=
  physicalPartialMonoid successorGraph allowedComponentTypes

/-- A physical family of E289 states. -/
abbrev E289PhysicalFamily := PhysicalFamily.{0, v} E289State

/-- A finite physical family of E289 states. -/
abbrev E289FinitePhysicalFamily := FinitePhysicalFamily.{0, v} E289State

/-! ## Grade and reciprocal additivity on direct compatibility -/

variable {I : Type v} [Fintype I]

theorem stateProfile_naryUnion {S : I → E289State} (hS : NaryCompatible S) :
    stateProfile (naryUnion S hS) = ∑ i, stateProfile (S i) :=
  componentProfile_naryUnion hS

theorem grade_naryUnion {S : I → E289State} (hS : NaryCompatible S) :
    grade (naryUnion S hS) = ∑ i, grade (S i) := by
  rw [grade, stateProfile_naryUnion hS, map_sum]
  rfl

theorem reciprocalValue_naryUnion {S : I → E289State} (hS : NaryCompatible S) :
    reciprocalValue (naryUnion S hS) = ∑ i, reciprocalValue (S i) := by
  simp only [reciprocalValue]
  exact vertexFold_naryUnion reciprocalWeight hS

theorem reciprocalValuePos_naryUnion {S : I → E289State} (hS : NaryCompatible S) :
    reciprocalValuePos (naryUnion S hS) = ∑ i, reciprocalValuePos (S i) := by
  apply NNRat.coe_injective
  simp only [NNRat.cast_sum, coe_reciprocalValuePos]
  exact reciprocalValue_naryUnion hS

theorem stateProfile_finitePhysicalUnion (S : E289NaryPhysicalDomain I) :
    stateProfile (finitePhysicalUnion S) = ∑ i, stateProfile (S.1 i) :=
  componentProfile_finitePhysicalUnion S

theorem grade_finitePhysicalUnion (S : E289NaryPhysicalDomain I) :
    grade (finitePhysicalUnion S) = ∑ i, grade (S.1 i) :=
  grade_naryUnion S.2

theorem reciprocalValue_finitePhysicalUnion (S : E289NaryPhysicalDomain I) :
    reciprocalValue (finitePhysicalUnion S) = ∑ i, reciprocalValue (S.1 i) := by
  simp only [reciprocalValue]
  exact vertexFold_finitePhysicalUnion reciprocalWeight S

/-! ## Component and interval facts -/

private theorem successorDist_le_one_between {x y w : ℕ+}
    (h : successorDist x y ≤ 1) (hw : w ∈ Set.uIcc x y) : w = x ∨ w = y := by
  rw [Set.mem_uIcc] at hw
  simp only [successorDist] at h
  simp only [← PNat.coe_le_coe, ← PNat.coe_inj] at hw ⊢
  omega

private theorem mem_uIcc_split {a b c w : ℕ+} (hw : w ∈ Set.uIcc a c) :
    w ∈ Set.uIcc a b ∨ w ∈ Set.uIcc b c := by
  simp only [Set.mem_uIcc, ← PNat.coe_le_coe] at hw ⊢
  omega

/-- The positive integer underlying a vertex of an induced successor
subgraph. -/
private def graphVertex {S : Set successorGraph}
    (x : (inducedGraph successorGraph S).carrier) : ℕ+ := x.1

private theorem eqvGen_uIcc {S : Set successorGraph} :
    ∀ {x y : (inducedGraph successorGraph S).carrier},
      Relation.EqvGen (inducedGraph successorGraph S).Rel x y →
        ∀ w : ℕ+, w ∈ Set.uIcc (graphVertex x) (graphVertex y) →
          ∃ hw : w ∈ S,
            Relation.EqvGen (inducedGraph successorGraph S).Rel ⟨w, hw⟩ x := by
  intro x y h
  induction h with
  | rel a b hab =>
      intro w hw
      rcases successorDist_le_one_between hab hw with rfl | rfl
      · exact ⟨a.2, Relation.EqvGen.refl a⟩
      · exact ⟨b.2, Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hab)⟩
  | refl a =>
      intro w hw
      rw [Set.uIcc_self, Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨a.2, Relation.EqvGen.refl a⟩
  | symm a b hab ih =>
      intro w hw
      rw [Set.uIcc_comm] at hw
      obtain ⟨hw', hgen⟩ := ih w hw
      exact ⟨hw', Relation.EqvGen.trans _ _ _ hgen hab⟩
  | trans a b c hab _ ihab ihbc =>
      intro w hw
      rcases mem_uIcc_split (b := graphVertex b) hw with hleft | hright
      · exact ihab w hleft
      · obtain ⟨hw', hgen⟩ := ihbc w hright
        exact ⟨hw', Relation.EqvGen.trans _ _ _ hgen
          (Relation.EqvGen.symm _ _ hab)⟩

/-- Connected components of a state are intervals: every vertex between two
vertices of one component again lies in the state, in that same component. -/
theorem component_mem_uIcc (S : E289State) (c : S.Components) {u v : ℕ+}
    (hu : u ∈ S.support) (hv : v ∈ S.support)
    (hcu : piZeroMk S.graph ⟨u, hu⟩ = c) (hcv : piZeroMk S.graph ⟨v, hv⟩ = c)
    {w : ℕ+} (hw : w ∈ Set.uIcc u v) :
    ∃ hw' : w ∈ S.support, piZeroMk S.graph ⟨w, hw'⟩ = c := by
  have hgen : Relation.EqvGen S.graph.Rel ⟨u, hu⟩ ⟨v, hv⟩ :=
    Quotient.exact (hcu.trans hcv.symm)
  obtain ⟨hw', hwgen⟩ := eqvGen_uIcc hgen w hw
  exact ⟨hw', (Quotient.sound hwgen).trans hcu⟩

/-- The support of a state is closed under passing between two vertices of one
connected component. -/
theorem mem_support_of_mem_uIcc (S : E289State) {u v : ℕ+}
    (hu : u ∈ S.support) (hv : v ∈ S.support)
    (hsame : piZeroMk S.graph ⟨u, hu⟩ = piZeroMk S.graph ⟨v, hv⟩)
    {w : ℕ+} (hw : w ∈ Set.uIcc u v) : w ∈ S.support :=
  (component_mem_uIcc S _ hu hv rfl hsame.symm hw).1

/-- Every component of an E289 state is binary or ternary. -/
theorem componentCardinality_eq_two_or_three (S : E289State) (c : S.Components) :
    componentCardinality successorGraph S.support S.support_finite c = 2 ∨
      componentCardinality successorGraph S.support S.support_finite c = 3 :=
  S.admissible c

/-! ## Finite physical constraints -/

/-- A finite physical constraint `c = (E,s)`: a finite forbidden vertex support
together with an integer margin at least one. -/
structure PhysicalConstraint where
  /-- The finite forbidden vertex support `E ↪ V₊`. -/
  forbidden : Finset ℕ+
  /-- The integer margin `s`. -/
  margin : ℕ
  /-- The margin is at least one. -/
  one_le_margin : 1 ≤ margin

/-- Admissibility of a state for a finite physical constraint: every state
vertex is at distance more than the margin from the forbidden support, and
vertices in distinct connected components are at distance more than the
margin. -/
def ConstraintAdmissible (c : PhysicalConstraint) (S : E289State) : Prop :=
  (∀ e ∈ c.forbidden, ∀ v : ℕ+, v ∈ S.support → c.margin < successorDist e v) ∧
    (∀ u v : S.graph, piZeroMk S.graph u ≠ piZeroMk S.graph v →
      c.margin < successorDist u.1 v.1)

/-- A physical family is `c`-admissible when every branch is. -/
def FamilyConstraintAdmissible (c : PhysicalConstraint)
    (F : E289PhysicalFamily.{v}) : Prop :=
  ∀ b : F.left, ConstraintAdmissible c (F.hom b)

/-- Constraint strengthening: a larger forbidden support and a larger margin. -/
instance : Preorder PhysicalConstraint where
  le c c' := c.forbidden ⊆ c'.forbidden ∧ c.margin ≤ c'.margin
  le_refl _ := ⟨subset_rfl, le_rfl⟩
  le_trans _ _ _ hab hbc := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

theorem constraint_le_iff (c c' : PhysicalConstraint) :
    c ≤ c' ↔ c.forbidden ⊆ c'.forbidden ∧ c.margin ≤ c'.margin :=
  Iff.rfl

/-- The common strengthening of two constraints. -/
def constraintJoin (c c' : PhysicalConstraint) : PhysicalConstraint where
  forbidden := c.forbidden ∪ c'.forbidden
  margin := max c.margin c'.margin
  one_le_margin := c.one_le_margin.trans (le_max_left _ _)

theorem le_constraintJoin_left (c c' : PhysicalConstraint) :
    c ≤ constraintJoin c c' :=
  ⟨Finset.subset_union_left, le_max_left _ _⟩

theorem le_constraintJoin_right (c c' : PhysicalConstraint) :
    c' ≤ constraintJoin c c' :=
  ⟨Finset.subset_union_right, le_max_right _ _⟩

/-- The constraint preorder is filtered. -/
theorem constraint_directed (c c' : PhysicalConstraint) :
    ∃ d : PhysicalConstraint, c ≤ d ∧ c' ≤ d :=
  ⟨constraintJoin c c', le_constraintJoin_left c c', le_constraintJoin_right c c'⟩

/-- The complete vertex support of a physical family. -/
def completeSupport (F : E289PhysicalFamily.{v}) : Set successorGraph :=
  ⋃ b : F.left, (F.hom b).support

theorem completeSupport_finite (F : E289FinitePhysicalFamily.{v}) :
    (completeSupport F.family).Finite := by
  haveI : Finite F.family.left := F.finite_domain
  exact Set.finite_iUnion fun b ↦ (F.family.hom b).support_finite

/-- `strengthen c F` adjoins the complete finite vertex support of all branches
of `F` to the forbidden support and preserves the margin. -/
noncomputable def strengthen (c : PhysicalConstraint)
    (F : E289FinitePhysicalFamily.{v}) : PhysicalConstraint where
  forbidden := c.forbidden ∪ (completeSupport_finite F).toFinset
  margin := c.margin
  one_le_margin := c.one_le_margin

theorem le_strengthen (c : PhysicalConstraint) (F : E289FinitePhysicalFamily.{v}) :
    c ≤ strengthen c F :=
  ⟨Finset.subset_union_left, le_rfl⟩

theorem mem_strengthen_forbidden (c : PhysicalConstraint)
    (F : E289FinitePhysicalFamily.{v}) {v : ℕ+}
    (hv : v ∈ completeSupport F.family) : v ∈ (strengthen c F).forbidden :=
  Finset.mem_union_right _ ((completeSupport_finite F).mem_toFinset.2 hv)

theorem strengthen_margin (c : PhysicalConstraint)
    (F : E289FinitePhysicalFamily.{v}) : (strengthen c F).margin = c.margin :=
  rfl

end Erdos289
