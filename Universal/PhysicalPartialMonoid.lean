import Universal.NaryCompatibility

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# The physical partial-monoid carrier

The binary operation is ambient union restricted to the binary direct
compatibility locus.  Finite multiplication is retained in its canonical
direct n-ary form, so its domain and value do not depend on a proof-local
parenthesization.
-/

open CategoryTheory
open scoped BigOperators

namespace Erdos289

universe u v w

variable {G : Graphᵣ.{u}} {Θ : Set ℕ+}

/-- Two states, regarded as a family indexed by `Fin 2`. -/
def binaryStateFamily (S T : FiniteComponentState G Θ) :
    Fin 2 → FiniteComponentState G Θ :=
  fun i ↦ if i = 0 then S else T

@[simp]
theorem binaryStateFamily_zero (S T : FiniteComponentState G Θ) :
    binaryStateFamily S T 0 = S :=
  by simp [binaryStateFamily]

@[simp]
theorem binaryStateFamily_one (S T : FiniteComponentState G Θ) :
    binaryStateFamily S T 1 = T :=
  by simp [binaryStateFamily]

private theorem binaryStateFamily_profile_sum_comm
    (S T : FiniteComponentState G Θ) :
    (∑ i, componentProfile (binaryStateFamily S T i)) =
      ∑ i, componentProfile (binaryStateFamily T S i) := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [binaryStateFamily, add_comm]

/-- The binary physical domain. -/
def BinaryPhysicalDomain (G : Graphᵣ.{u}) (Θ : Set ℕ+) :=
  {p : FiniteComponentState G Θ × FiniteComponentState G Θ //
    NaryCompatible (binaryStateFamily p.1 p.2)}

/-- Binary direct compatibility is symmetric. -/
theorem binaryCompatible_comm (S T : FiniteComponentState G Θ) :
    NaryCompatible (binaryStateFamily S T) ↔
      NaryCompatible (binaryStateFamily T S) := by
  constructor <;> intro h
  · apply naryCompatible_of_support_profile_eq h
    · ext x
      simp [narySupport, binaryStateFamily, or_comm]
    · exact (binaryStateFamily_profile_sum_comm S T).symm
  · apply naryCompatible_of_support_profile_eq h
    · ext x
      simp [narySupport, binaryStateFamily, or_comm]
    · exact binaryStateFamily_profile_sum_comm S T

/-- Swap the two operands in the binary physical domain. -/
def binaryPhysicalSwap (p : BinaryPhysicalDomain G Θ) : BinaryPhysicalDomain G Θ :=
  ⟨(p.1.2, p.1.1), (binaryCompatible_comm p.1.1 p.1.2).mp p.2⟩

/-- Binary physical multiplication: union on the binary compatible locus. -/
noncomputable def binaryUnion (p : BinaryPhysicalDomain G Θ) :
    FiniteComponentState G Θ :=
  naryUnion (binaryStateFamily p.1.1 p.1.2) p.2

/-- Binary physical multiplication is commutative. -/
theorem binaryUnion_comm (p : BinaryPhysicalDomain G Θ) :
    binaryUnion (binaryPhysicalSwap p) = binaryUnion p := by
  apply FiniteComponentState.ext
  ext x
  simp [binaryUnion, binaryPhysicalSwap, naryUnion, narySupport, binaryStateFamily, or_comm]

/-- The direct finite physical multiplication locus. -/
def FiniteMultiplicationDomain (G : Graphᵣ.{u}) (Θ : Set ℕ+)
    (I : Type v) [Fintype I] : Set (I → FiniteComponentState G Θ) :=
  {S | NaryCompatible S}

/-- The direct finite physical multiplication domain as a subtype. -/
def NaryPhysicalDomain (G : Graphᵣ.{u}) (Θ : Set ℕ+) (I : Type v) [Fintype I] :=
  FiniteMultiplicationDomain G Θ I

/-- Direct finite multiplication on its canonical n-ary domain. -/
noncomputable def finitePhysicalUnion {I : Type v} [Fintype I]
    (S : NaryPhysicalDomain G Θ I) : FiniteComponentState G Θ :=
  naryUnion S.1 S.2

/-- Finite physical multiplication is independent of the proof witnessing its
direct compatibility domain; hence no parenthesization data enters its value. -/
theorem finitePhysicalUnion_witness_independent {I : Type v} [Fintype I]
    (S : I → FiniteComponentState G Θ) (h h' : NaryCompatible S) :
    finitePhysicalUnion (⟨S, h⟩ : NaryPhysicalDomain G Θ I) =
      finitePhysicalUnion (⟨S, h'⟩ : NaryPhysicalDomain G Θ I) := by
  rfl

/-- Membership in the finite multiplication domain is exactly direct n-ary
compatibility. -/
theorem mem_naryPhysicalDomain_iff {I : Type v} [Fintype I]
    (S : I → FiniteComponentState G Θ) :
    S ∈ FiniteMultiplicationDomain G Θ I ↔ NaryCompatible S :=
  Iff.rfl

/-- The finite physical product is the ambient union, independently of its
compatibility witness. -/
theorem finitePhysicalUnion_support {I : Type v} [Fintype I]
    (S : NaryPhysicalDomain G Θ I) :
    (finitePhysicalUnion S).support = narySupport S.1 :=
  rfl

/-- The component profile is additive on every finite multiplication domain. -/
theorem componentProfile_finitePhysicalUnion {I : Type v} [Fintype I]
    (S : NaryPhysicalDomain G Θ I) :
    componentProfile (finitePhysicalUnion S) = ∑ i, componentProfile (S.1 i) :=
  componentProfile_naryUnion S.2

/-- Every vertex-local commutative-monoid observable is additive on every
finite multiplication domain. -/
theorem vertexFold_finitePhysicalUnion {I : Type v} [Fintype I]
    {L : Type w} [AddCommMonoid L] (weight : G → L)
    (S : NaryPhysicalDomain G Θ I) :
    vertexFold weight (finitePhysicalUnion S) = ∑ i, vertexFold weight (S.1 i) :=
  vertexFold_naryUnion weight S.2

/-- The empty physical state. -/
def emptyPhysicalState (G : Graphᵣ.{u}) (Θ : Set ℕ+) :
    FiniteComponentState G Θ where
  support := ∅
  support_finite := Set.finite_empty
  admissible := fun c ↦ by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    exact x.2.elim

@[simp]
theorem componentProfile_emptyPhysicalState (G : Graphᵣ.{u}) (Θ : Set ℕ+) :
    componentProfile (emptyPhysicalState G Θ) = 0 := by
  classical
  rw [componentProfile]
  apply Finset.sum_eq_zero
  intro c _
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  exact x.2.elim

/-- The empty state is compatible on the left with every state. -/
theorem emptyPhysicalState_left_compatible (S : FiniteComponentState G Θ) :
    NaryCompatible (binaryStateFamily (emptyPhysicalState G Θ) S) := by
  let B := binaryStateFamily (emptyPhysicalState G Θ) S
  have hsupp : narySupport B = S.support := by
    ext x
    simp [B, narySupport, binaryStateFamily, emptyPhysicalState]
  have hadmAll : IsAdmissibleSupport G Θ (narySupport B) := by
    rw [hsupp]
    intro hA c
    simpa only using S.admissible c
  let hadm := hadmAll (narySupport_finite B)
  apply naryCompatible_maximal B hadm
  have hstate : naryUnionOfAdmissible B hadm = S := by
    apply FiniteComponentState.ext
    exact hsupp
  rw [hstate, Fin.sum_univ_two]
  simp [B]

/-- The empty state is compatible on the right with every state. -/
theorem emptyPhysicalState_right_compatible (S : FiniteComponentState G Θ) :
    NaryCompatible (binaryStateFamily S (emptyPhysicalState G Θ)) :=
  (binaryCompatible_comm (emptyPhysicalState G Θ) S).mp
    (emptyPhysicalState_left_compatible S)

/-- The canonical left-unit point of the binary domain. -/
def emptyPhysicalStateLeftDomain (S : FiniteComponentState G Θ) :
    BinaryPhysicalDomain G Θ :=
  ⟨(emptyPhysicalState G Θ, S), emptyPhysicalState_left_compatible S⟩

/-- The canonical right-unit point of the binary domain. -/
def emptyPhysicalStateRightDomain (S : FiniteComponentState G Θ) :
    BinaryPhysicalDomain G Θ :=
  ⟨(S, emptyPhysicalState G Θ), emptyPhysicalState_right_compatible S⟩

@[simp]
theorem binaryUnion_empty_left (S : FiniteComponentState G Θ) :
    binaryUnion (emptyPhysicalStateLeftDomain S) = S := by
  apply FiniteComponentState.ext
  ext x
  simp [binaryUnion, emptyPhysicalStateLeftDomain, naryUnion, narySupport,
    binaryStateFamily, emptyPhysicalState]

@[simp]
theorem binaryUnion_empty_right (S : FiniteComponentState G Θ) :
    binaryUnion (emptyPhysicalStateRightDomain S) = S := by
  apply FiniteComponentState.ext
  ext x
  simp [binaryUnion, emptyPhysicalStateRightDomain, naryUnion, narySupport,
    binaryStateFamily, emptyPhysicalState]

/-- The binary data of the physical partial-monoid shadow.  Its finite domains
and products are `FiniteMultiplicationDomain` and `finitePhysicalUnion`. -/
structure PhysicalPartialMonoid (G : Graphᵣ.{u}) (Θ : Set ℕ+) where
  /-- Unit state. -/
  unit : FiniteComponentState G Θ
  /-- Domain of binary multiplication. -/
  binaryDomain : Set (FiniteComponentState G Θ × FiniteComponentState G Θ)
  /-- Multiplication on its domain. -/
  multiply : binaryDomain → FiniteComponentState G Θ

/-- The physical partial-monoid data supplied by direct compatibility and
ambient union. -/
noncomputable def physicalPartialMonoid (G : Graphᵣ.{u}) (Θ : Set ℕ+) :
    PhysicalPartialMonoid G Θ where
  unit := emptyPhysicalState G Θ
  binaryDomain := {p | NaryCompatible (binaryStateFamily p.1 p.2)}
  multiply := binaryUnion

/-- A physical family over a state object `C` is an object of `Type / C`. -/
abbrev PhysicalFamily (C : Type u) := CategoryTheory.Over (X := C)

/-- A physical family whose domain is finite. -/
structure FinitePhysicalFamily (C : Type u) where
  /-- The underlying object of `Type / C`. -/
  family : PhysicalFamily C
  /-- Finiteness of its branch type. -/
  finite_domain : Finite family.left

namespace FinitePhysicalFamily

instance {C : Type u} (F : FinitePhysicalFamily C) : Finite F.family.left :=
  F.finite_domain

end FinitePhysicalFamily

/-- A binary family pair factors through the binary physical domain. -/
def AllCompatible
    (F R : PhysicalFamily (FiniteComponentState G Θ)) : Prop :=
  ∃ lift : F.left × R.left → BinaryPhysicalDomain G Θ,
    ∀ x, (lift x).1 = (F.hom x.1, R.hom x.2)

theorem allCompatible_iff
    (F R : PhysicalFamily (FiniteComponentState G Θ)) :
    AllCompatible F R ↔
      ∀ f : F.left, ∀ r : R.left,
        NaryCompatible (binaryStateFamily (F.hom f) (R.hom r)) := by
  constructor
  · rintro ⟨lift, hlift⟩ f r
    have h := (lift (f, r)).2
    simpa [hlift (f, r)] using h
  · intro h
    refine ⟨fun x ↦ ⟨(F.hom x.1, R.hom x.2), h x.1 x.2⟩, fun _ ↦ rfl⟩

/-- A finite indexed family of physical families factors through the direct
n-ary physical locus. -/
def NaryFamilyCompatible {I : Type v} [Fintype I]
    (F : I → PhysicalFamily (FiniteComponentState G Θ)) : Prop :=
  ∃ lift : (∀ i, (F i).left) → NaryPhysicalDomain G Θ I,
    ∀ x i, (lift x).1 i = (F i).hom (x i)

theorem naryFamilyCompatible_iff {I : Type v} [Fintype I]
    (F : I → PhysicalFamily (FiniteComponentState G Θ)) :
    NaryFamilyCompatible F ↔
      ∀ x : ∀ i, (F i).left,
        NaryCompatible fun i ↦ (F i).hom (x i) := by
  constructor
  · rintro ⟨lift, hlift⟩ x
    have h := (lift x).2
    change NaryCompatible (lift x).1 at h
    have heq : (lift x).1 = fun i ↦ (F i).hom (x i) := funext (hlift x)
    simpa only [heq] using h
  · intro h
    refine ⟨fun x ↦ ⟨fun i ↦ (F i).hom (x i), h x⟩, fun _ _ ↦ rfl⟩

end Erdos289
