module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.CyclicRow
public import Erdos289.StageProfile
public import Erdos289.TailComposition

@[expose] public section

/-!
# The state system available at one current

A pool of transverse atoms is not everything a current has to offer: states
whose residue already lies in the lower stage — class zero in the simple fibre
— are equally usable, and they are what lets a single nonzero class fill the
whole fibre at a prescribed grade.  A transverse pool cannot hold them, because
transversality is nonvanishing in the fibre.

`LocalStateSystem` is therefore the object the local target should be stated
over: a finite family of pairwise compatible admissible states, each factoring
through the current stage, with no condition on their classes.  A compatible
transverse pool is one, and so is that pool together with any compatible family
of class-zero states.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/-- A finite compatible family of admissible states at one current. -/
structure LocalStateSystem (Q : ℕ) (c : PhysicalConstraint) where
  /-- The states. -/
  atoms : Finset Support
  admissible : ∀ S ∈ atoms, S.Admissible smallBlockSizes c
  factors : ∀ S ∈ atoms, S.FactorsThroughPrimePowerStage Q
  compatible : (atoms : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c

namespace LocalStateSystem

variable {Q : ℕ} {c : PhysicalConstraint}

/-- The simple-fibre class of a state, as a total function. -/
noncomputable def classOf (L : LocalStateSystem Q c) (S : Support) :
    PrimePowerSimpleFibre Q := by
  classical
  exact if h : S ∈ L.atoms then S.simpleFibreClass (L.factors S h) else 0

theorem classOf_eq (L : LocalStateSystem Q c) {S : Support} (hS : S ∈ L.atoms)
    (hfac : S.FactorsThroughPrimePowerStage Q) :
    L.classOf S = S.simpleFibreClass hfac := by
  classical
  rw [classOf, dif_pos hS]

/--
The local target of the current, over the whole state system: every class of
the simple fibre is the class of a compatible subfamily of exactly `h` states,
of aggregate grade `h` and mass at most `h · maxMass`.
-/
def CoversAtGrade (L : LocalStateSystem Q c) (h : ℕ) (maxMass : ℚ) : Prop :=
  ∀ x : PrimePowerSimpleFibre Q, ∃ A : Finset Support, A ⊆ L.atoms ∧ A.card = h ∧
    (A : Set Support).Pairwise (fun S T ↦ S.CompatibleFor T c) ∧
    (aggregateSupport A).grade = h ∧
    (aggregateSupport A).value ≤ h * maxMass ∧
    ∀ hfac : (aggregateSupport A).FactorsThroughPrimePowerStage Q,
      (aggregateSupport A).simpleFibreClass hfac = x

/-- A compatible transverse pool is a state system. -/
def ofPool (P : CompatibleTransversePool Q c) : LocalStateSystem Q c where
  atoms := P.atoms
  admissible := P.admissible
  factors := fun S hS => Classical.choose (P.transverse S hS)
  compatible := P.compatible

@[simp]
theorem ofPool_atoms (P : CompatibleTransversePool Q c) : (ofPool P).atoms = P.atoms := rfl

theorem coversAtGrade_ofPool {P : CompatibleTransversePool Q c} {h : ℕ} {maxMass : ℚ}
    (hcov : P.CoversAtGrade h maxMass) : (ofPool P).CoversAtGrade h maxMass := hcov

/--
Adjoining compatible class-zero states to a state system.  The hypothesis is
compatibility across the two families and admissibility of the new ones; their
classes are not constrained here, only in the theorems that use them.
-/
def adjoin (L : LocalStateSystem Q c) (N : Finset Support)
    (hadm : ∀ S ∈ N, S.Admissible smallBlockSizes c)
    (hfac : ∀ S ∈ N, S.FactorsThroughPrimePowerStage Q)
    (hpairN : (N : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c)
    (hcross : ∀ S ∈ L.atoms, ∀ T ∈ N, S.CompatibleFor T c) :
    LocalStateSystem Q c where
  atoms := L.atoms ∪ N
  admissible := by
    intro S hS
    rcases Finset.mem_union.1 hS with h | h
    · exact L.admissible S h
    · exact hadm S h
  factors := by
    intro S hS
    rcases Finset.mem_union.1 hS with h | h
    · exact L.factors S h
    · exact hfac S h
  compatible := by
    intro S hS T hT hST
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hS hT
    rcases hS with hS | hS <;> rcases hT with hT | hT
    · exact L.compatible hS hT hST
    · exact hcross S hS T hT
    · refine ⟨(hcross T hT S hS).1.symm, fun x hx y hy => ?_⟩
      have hd := (hcross T hT S hS).2 y hy x hx
      have hcomm := Nat.dist_comm x.1 y.1
      omega
    · exact hpairN hS hT hST

@[simp]
theorem adjoin_atoms (L : LocalStateSystem Q c) (N : Finset Support)
    (hadm) (hfac) (hpairN) (hcross) :
    (L.adjoin N hadm hfac hpairN hcross).atoms = L.atoms ∪ N := rfl

end LocalStateSystem

/--
A state system reaching its local target at grade `h`, all of whose states lie
inside a finite footprint, is a tail stage from the lower stage to the current
one.
-/
theorem tailStage_of_localSystem
    {Q : ℕ} {c : PhysicalConstraint} (L : LocalStateSystem Q c)
    {h : ℕ} {maxMass : ℚ} (hcov : L.CoversAtGrade h maxMass)
    {F : Support} (hfoot : ∀ S ∈ L.atoms, S ⊆ F) :
    TailStage c F (lowerPrimePowerStage Q) (primePowerStage Q) h (h * maxMass) := by
  classical
  intro v hv
  obtain ⟨A, hAsub, -, hApair, hAgrade, hAvalue, hAclass⟩ :=
    hcov (QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) (⟨v, hv⟩ : primePowerStage Q))
  have hfac : ∀ S ∈ A, S.FactorsThroughPrimePowerStage Q :=
    fun S hS => L.factors S (hAsub hS)
  have hagg := aggregateSupport_factorsThrough hApair hfac
  refine ⟨aggregateSupport A, ?_,
    aggregateSupport_admissible (fun S hS => L.admissible S (hAsub hS)) hApair,
    hAgrade, ?_, Support.value_nonneg _, hAvalue⟩
  · intro x hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
    exact hfoot S (hAsub hS) hxS
  · refine (simpleFibre_mk_eq_iff_sub_mem hagg hv).1 ?_
    exact hAclass hagg

end Erdos289
