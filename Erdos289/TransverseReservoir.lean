module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimePowerFiltration
public import Erdos289.PhysicalSupports

@[expose] public section

/-!
# Filtered-transverse physical reservoirs

This is the intrinsic output of the signed-inverse arithmetic and physical
packing layers.  A support is transverse when its centered observation factors
through the current compact stage and has nonzero image in the associated
simple quotient.  Modular inverses, orientations, denominator factorizations,
centres, and conflict graphs are deliberately absent from this interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- A support observation factors through the current compact stage. -/
def Support.FactorsThroughPrimePowerStage (S : Support) (Q : ℕ) : Prop :=
  S.residue ∈ primePowerStage Q

/-- The canonical class of a factored observation in the simple quotient. -/
def Support.simpleFibreClass {S : Support} {Q : ℕ}
    (hS : S.FactorsThroughPrimePowerStage Q) : PrimePowerSimpleFibre Q :=
  QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) ⟨S.residue, hS⟩

/-- Nonvanishing in the simple fibre is exactly escape from the lower stage. -/
theorem Support.simpleFibreClass_ne_zero_iff {S : Support} {Q : ℕ}
    (hS : S.FactorsThroughPrimePowerStage Q) :
    S.simpleFibreClass hS ≠ 0 ↔ S.residue ∉ lowerPrimePowerStage Q := by
  change S.residue ∈ primePowerStage Q at hS
  change (QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q)
      (⟨S.residue, hS⟩ : primePowerStage Q) ≠ 0) ↔ _
  let x : primePowerStage Q := ⟨S.residue, hS⟩
  constructor
  · intro hclass hlower
    apply hclass
    apply (QuotientAddGroup.eq_zero_iff x).2
    exact hlower
  · intro hlower hclass
    apply hlower
    exact (QuotientAddGroup.eq_zero_iff x).1 hclass

/-- The class in the simple quotient depends only on the support. -/
theorem Support.simpleFibreClass_congr {S : Support} {Q : ℕ}
    (h₁ h₂ : S.FactorsThroughPrimePowerStage Q) :
    S.simpleFibreClass h₁ = S.simpleFibreClass h₂ := rfl

/-- Intrinsic filtered transversality at a prime-power stage. -/
def Support.FilteredTransverse (S : Support) (Q : ℕ) : Prop :=
  ∃ hS : S.FactorsThroughPrimePowerStage Q, S.simpleFibreClass hS ≠ 0

/-- The intrinsic nonzero simple-fibre point carried by a transverse support. -/
noncomputable def Support.transverseClass {S : Support} {Q : ℕ}
    (hS : S.FilteredTransverse Q) : PrimePowerSimpleFibre Q :=
  S.simpleFibreClass (Classical.choose hS)

theorem Support.transverseClass_ne_zero {S : Support} {Q : ℕ}
    (hS : S.FilteredTransverse Q) : S.transverseClass hS ≠ 0 :=
  (Classical.choose_spec hS)

/-- The transverse class depends only on the support. -/
theorem Support.transverseClass_congr {S : Support} {Q : ℕ}
    (h₁ h₂ : S.FilteredTransverse Q) :
    S.transverseClass h₁ = S.transverseClass h₂ := rfl

/-- The transverse class is the simple-fibre class of any factorization. -/
theorem Support.transverseClass_eq_simpleFibreClass {S : Support} {Q : ℕ}
    (hS : S.FilteredTransverse Q) (hfac : S.FactorsThroughPrimePowerStage Q) :
    S.transverseClass hS = S.simpleFibreClass hfac := rfl

/-- A finite physical reservoir before global compatibility selection. -/
structure TransverseReservoir (Q : ℕ) (c : PhysicalConstraint) where
  atoms : Finset Support
  admissible : ∀ S ∈ atoms, S.Admissible smallBlockSizes c
  transverse : ∀ S ∈ atoms, S.FilteredTransverse Q

namespace TransverseReservoir

/-- The simple-fibre class of an atom, as a total function on supports.  Off
the reservoir the value is irrelevant and is set to zero; on it the value is
the atom's transverse class. -/
noncomputable def classOf {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (S : Support) : PrimePowerSimpleFibre Q := by
  classical
  exact if h : S ∈ R.atoms then S.transverseClass (R.transverse S h) else 0

theorem classOf_eq {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) {S : Support} (hS : S ∈ R.atoms)
    (hfac : S.FactorsThroughPrimePowerStage Q) :
    R.classOf S = S.simpleFibreClass hfac := by
  classical
  rw [classOf, dif_pos hS]
  rfl

/-- The canonical fibre over one simple-quotient value. -/
noncomputable def simpleValueFibre {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (x : PrimePowerSimpleFibre Q) :
    Finset {S // S ∈ R.atoms} := by
  classical
  exact R.atoms.attach.filter fun S ↦
    S.1.transverseClass (R.transverse S.1 S.2) = x

/-- Canonical image of a reservoir in the associated simple fibre. -/
noncomputable def simpleValues {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) : Finset (PrimePowerSimpleFibre Q) := by
  classical
  exact R.atoms.attach.image fun S ↦
    S.1.transverseClass (R.transverse S.1 S.2)

theorem mem_simpleValueFibre_iff {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (x : PrimePowerSimpleFibre Q)
    (S : {S // S ∈ R.atoms}) :
    S ∈ R.simpleValueFibre x ↔
      S.1.transverseClass (R.transverse S.1 S.2) = x := by
  classical
  simp [simpleValueFibre]

theorem mem_simpleValues_iff {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (v : PrimePowerSimpleFibre Q) :
    v ∈ R.simpleValues ↔
      ∃ S : {S // S ∈ R.atoms}, S.1.transverseClass (R.transverse S.1 S.2) = v := by
  classical
  constructor
  · intro hv
    obtain ⟨S, -, hS⟩ := Finset.mem_image.mp hv
    exact ⟨S, hS⟩
  · rintro ⟨S, rfl⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ _)

theorem simpleValues_nonzero {Q : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) {x : PrimePowerSimpleFibre Q}
    (hx : x ∈ R.simpleValues) : x ≠ 0 := by
  classical
  rw [simpleValues, Finset.mem_image] at hx
  rcases hx with ⟨S, hS, rfl⟩
  exact Support.transverseClass_ne_zero (R.transverse S.1 S.2)

end TransverseReservoir

/-- The canonical binary compatibility relation inside one physical constraint. -/
def Support.CompatibleFor (S T : Support) (c : PhysicalConstraint) : Prop :=
  S.GraphDisjoint T ∧ S.CrossSeparated T c.separation

/-- Intrinsic conflicts of one atom inside a reservoir. -/
noncomputable def TransverseReservoir.conflictNeighbors
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    (S : Support) : Finset Support := by
  classical
  exact R.atoms.filter fun T ↦ T ≠ S ∧ ¬S.CompatibleFor T c

/-- Quantitative filtered-transverse output.  Arithmetic coefficients,
orientations, inverse representatives, and carrier labels are intentionally
absent.  The fields record exactly the four quantities used downstream:
row size, simple-fibre multiplicity, physical mass, and conflict degree. -/
structure QuantitativeTransverseReservoir
    (Q : ℕ) (c : PhysicalConstraint)
    (rowMin fibreMultiplicity conflictDegree : ℕ) (maxMass : ℚ)
    extends TransverseReservoir Q c where
  row_card : rowMin ≤ atoms.card
  fibre_card : ∀ x : PrimePowerSimpleFibre Q,
    (toTransverseReservoir.simpleValueFibre x).card ≤ fibreMultiplicity
  atom_mass : ∀ S ∈ atoms, S.value ≤ maxMass
  conflict_card : ∀ S ∈ atoms,
    (toTransverseReservoir.conflictNeighbors S).card ≤ conflictDegree

/-- A globally compatible point of the finite reservoir feasibility object. -/
structure CompatibleTransversePool (Q : ℕ) (c : PhysicalConstraint)
    extends TransverseReservoir Q c where
  compatible : (atoms : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c

namespace CompatibleTransversePool

/-- Every subpool remains an intrinsic compatible transverse pool. -/
def restrict {Q : ℕ} {c : PhysicalConstraint}
    (P : CompatibleTransversePool Q c) (A : Finset Support) (hA : A ⊆ P.atoms) :
    CompatibleTransversePool Q c where
  atoms := A
  admissible S hS := P.admissible S (hA hS)
  transverse S hS := P.transverse S (hA hS)
  compatible := P.compatible.mono (by
    intro S hS
    exact hA hS)

end CompatibleTransversePool

end Erdos289
