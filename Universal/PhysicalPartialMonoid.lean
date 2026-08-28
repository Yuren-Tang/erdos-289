import Universal.NaryCompatibility

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic.FinCases

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

/-- The empty physical state. -/
def emptyPhysicalState (G : Graphᵣ.{u}) (Θ : Set ℕ+) :
    FiniteComponentState G Θ where
  support := ∅
  support_finite := Set.finite_empty
  admissible := fun c ↦ by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    exact x.2.elim

theorem naryCompatible_reindex {I : Type v} {J : Type w}
    [Fintype I] [Fintype J] (e : J ≃ I)
    (S : I → FiniteComponentState G Θ) :
    NaryCompatible (fun j ↦ S (e j)) ↔ NaryCompatible S := by
  constructor
  · intro h
    have h' := naryCompatible_subfamily h e.symm.toEmbedding
    simpa using h'
  · intro h
    exact naryCompatible_subfamily h e.toEmbedding

private theorem narySupport_equiv {I : Type v} {J : Type w}
    [Fintype I] [Fintype J] (e : J ≃ I)
    (S : I → FiniteComponentState G Θ) :
    narySupport (fun j ↦ S (e j)) = narySupport S := by
  ext x
  simp only [narySupport, Set.mem_iUnion]
  constructor
  · rintro ⟨j, hx⟩
    exact ⟨e j, hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨e.symm i, by simpa⟩

private theorem sumFamily_compatible_of_binary
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ)
    (hleft : NaryCompatible fun i ↦ S (.inl i))
    (hright : NaryCompatible fun j ↦ S (.inr j))
    (hmerge : NaryCompatible (binaryStateFamily
      (naryUnion (fun i ↦ S (.inl i)) hleft)
      (naryUnion (fun j ↦ S (.inr j)) hright))) :
    NaryCompatible S := by
  apply (naryCompatible_sum_iff_grouping S).2
  refine ⟨hleft, hright, ?_⟩
  have heq : narySumGrouping S hleft hright =
      binaryStateFamily
        (naryUnion (fun i ↦ S (.inl i)) hleft)
        (naryUnion (fun j ↦ S (.inr j)) hright) := by
    funext k
    fin_cases k <;> simp [narySumGrouping, binaryStateFamily]
  rw [heq]
  exact hmerge

private theorem sumFamily_binary_of_compatible
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ) (hS : NaryCompatible S) :
    ∃ hleft : NaryCompatible (fun i ↦ S (.inl i)),
      ∃ hright : NaryCompatible (fun j ↦ S (.inr j)),
        NaryCompatible (binaryStateFamily
          (naryUnion (fun i ↦ S (.inl i)) hleft)
          (naryUnion (fun j ↦ S (.inr j)) hright)) := by
  obtain ⟨hleft, hright, hgroup⟩ :=
    (naryCompatible_sum_iff_grouping S).1 hS
  refine ⟨hleft, hright, ?_⟩
  have heq : narySumGrouping S hleft hright =
      binaryStateFamily
        (naryUnion (fun i ↦ S (.inl i)) hleft)
        (naryUnion (fun j ↦ S (.inr j)) hright) := by
    funext k
    fin_cases k <;> simp [narySumGrouping, binaryStateFamily]
  rw [← heq]
  exact hgroup

private theorem emptyFamily_compatible
    (S : PEmpty → FiniteComponentState G Θ) : NaryCompatible S := by
  constructor
  · intro p
    exact p.1.elim
  · exact naryComponentMap_surjective _

private theorem singletonFamily_compatible
    (S : PUnit → FiniteComponentState G Θ) : NaryCompatible S := by
  have hsupp : narySupport S = (S PUnit.unit).support := by
    ext x
    simp only [narySupport, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      simpa only [Subsingleton.elim i PUnit.unit] using hi
    · intro hx
      exact ⟨PUnit.unit, hx⟩
  have hadmAll : IsAdmissibleSupport G Θ (narySupport S) := by
    rw [hsupp]
    intro hA c
    simpa only using (S PUnit.unit).admissible c
  let hadm := hadmAll (narySupport_finite S)
  apply naryCompatible_maximal S hadm
  have hstate : naryUnionOfAdmissible S hadm = S PUnit.unit := by
    apply FiniteComponentState.ext
    exact hsupp
  rw [hstate]
  simp

/-- A full binary parenthesization shape, including the nullary and unary
products. -/
inductive PhysicalParenthesizationTree where
  | empty
  | leaf
  | node (left right : PhysicalParenthesizationTree)

/-- The leaf positions of a parenthesization shape. -/
@[reducible] def PhysicalParenthesizationTree.Leaves :
    PhysicalParenthesizationTree → Type
  | .empty => PEmpty
  | .leaf => PUnit
  | .node left right => left.Leaves ⊕ right.Leaves

@[instance_reducible] def PhysicalParenthesizationTree.fintypeLeaves :
    (t : PhysicalParenthesizationTree) → Fintype t.Leaves
  | .empty => inferInstance
  | .leaf => inferInstance
  | .node left right =>
      letI := left.fintypeLeaves
      letI := right.fintypeLeaves
      inferInstance

instance (t : PhysicalParenthesizationTree) : Fintype t.Leaves :=
  t.fintypeLeaves

/-- A genuine iterated binary evaluation: each internal node is defined
exactly when the two recursively evaluated child products lie in the binary
physical domain. -/
inductive IteratedBinaryEvaluation :
    (t : PhysicalParenthesizationTree) →
      (t.Leaves → FiniteComponentState G Θ) →
        FiniteComponentState G Θ → Prop
  | empty (S) :
      IteratedBinaryEvaluation .empty S (emptyPhysicalState G Θ)
  | leaf (S) :
      IteratedBinaryEvaluation .leaf S (S PUnit.unit)
  | node {left right S L R}
      (hleft : IteratedBinaryEvaluation left (fun i ↦ S (.inl i)) L)
      (hright : IteratedBinaryEvaluation right (fun j ↦ S (.inr j)) R)
      (hmerge : NaryCompatible (binaryStateFamily L R)) :
      IteratedBinaryEvaluation (.node left right) S
        (binaryUnion ⟨(L, R), hmerge⟩)

/-- Every recursively evaluated product has the ambient union of its leaves as
its underlying support. -/
theorem IteratedBinaryEvaluation.support {t : PhysicalParenthesizationTree}
    {S : t.Leaves → FiniteComponentState G Θ}
    {U : FiniteComponentState G Θ} (hU : IteratedBinaryEvaluation t S U) :
    U.support = narySupport S := by
  induction hU with
  | empty S =>
      ext x
      simp [emptyPhysicalState, narySupport]
  | leaf S =>
      ext x
      simp only [narySupport, Set.mem_iUnion]
      constructor
      · intro hx
        exact ⟨PUnit.unit, hx⟩
      · rintro ⟨i, hi⟩
        simpa only [Subsingleton.elim i PUnit.unit] using hi
  | node hleft hright hmerge ihleft ihrigh =>
      ext x
      simp [binaryUnion, naryUnion, narySupport, Fin.exists_fin_two,
        binaryStateFamily, ihleft, ihrigh]

/-- Every defined iterated binary value is the direct union of all leaves. -/
theorem IteratedBinaryEvaluation.eq_naryUnion
    {t : PhysicalParenthesizationTree}
    {S : t.Leaves → FiniteComponentState G Θ}
    {U : FiniteComponentState G Θ} (hU : IteratedBinaryEvaluation t S U)
    (hS : NaryCompatible S) :
    U = naryUnion S hS := by
  apply FiniteComponentState.ext
  exact hU.support

/-- The recursive binary domain of every shape is exactly its direct finite
compatibility locus. -/
theorem iteratedBinaryEvaluation_iff_naryCompatible
    (t : PhysicalParenthesizationTree)
    (S : t.Leaves → FiniteComponentState G Θ) :
    (∃ U, IteratedBinaryEvaluation t S U) ↔ NaryCompatible S := by
  induction t with
  | empty =>
      constructor
      · intro _
        exact emptyFamily_compatible S
      · intro _
        exact ⟨emptyPhysicalState G Θ, .empty S⟩
  | leaf =>
      constructor
      · intro _
        exact singletonFamily_compatible S
      · intro _
        exact ⟨S PUnit.unit, .leaf S⟩
  | node left right ihleft ihrigh =>
      constructor
      · rintro ⟨U, hU⟩
        cases hU with
        | node hleft hright hmerge =>
            let hleft' := (ihleft _).mp ⟨_, hleft⟩
            let hright' := (ihrigh _).mp ⟨_, hright⟩
            apply naryCompatible_of_support_profile_eq hmerge
            · ext x
              simp [narySupport, Fin.exists_fin_two, binaryStateFamily,
                hleft.support, hright.support]
            · rw [Fintype.sum_sum_type, Fin.sum_univ_two]
              simp only [binaryStateFamily_zero, binaryStateFamily_one]
              rw [← componentProfile_naryUnion hleft',
                ← componentProfile_naryUnion hright']
              congr 1
              · symm
                apply congrArg componentProfile
                apply FiniteComponentState.ext
                exact hleft.support
              · symm
                apply congrArg componentProfile
                apply FiniteComponentState.ext
                exact hright.support
      · intro hS
        obtain ⟨hleft, hright, hmerge⟩ :=
          sumFamily_binary_of_compatible S hS
        obtain ⟨L, hL⟩ := (ihleft _).mpr hleft
        obtain ⟨R, hR⟩ := (ihrigh _).mpr hright
        have hLdirect : L = naryUnion (fun i ↦ S (.inl i)) hleft := by
          apply FiniteComponentState.ext
          exact hL.support
        have hRdirect : R = naryUnion (fun j ↦ S (.inr j)) hright := by
          apply FiniteComponentState.ext
          exact hR.support
        subst L
        subst R
        exact ⟨_, .node hL hR hmerge⟩

/-- A parenthesization of a family indexed by `I` is a binary shape together
with an exact identification of its leaf occurrences with `I`. -/
structure BinaryParenthesization (I : Type v) where
  shape : PhysicalParenthesizationTree
  leavesEquiv : shape.Leaves ≃ I

/-- The domain obtained by evaluating a chosen finite parenthesization through
the actual binary physical multiplication. -/
def IteratedBinaryDomain {I : Type v} [Fintype I]
    (P : BinaryParenthesization I)
    (S : I → FiniteComponentState G Θ) : Prop :=
  ∃ U, IteratedBinaryEvaluation P.shape (fun l ↦ S (P.leavesEquiv l)) U

/-- Every finite parenthesized binary domain coincides exactly with the direct
n-ary compatibility locus. -/
theorem iteratedBinaryDomain_iff_naryCompatible
    {I : Type v} [Fintype I] (P : BinaryParenthesization I)
    (S : I → FiniteComponentState G Θ) :
    IteratedBinaryDomain P S ↔ NaryCompatible S := by
  rw [IteratedBinaryDomain, iteratedBinaryEvaluation_iff_naryCompatible]
  exact naryCompatible_reindex P.leavesEquiv S

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

/-- Every valid binary parenthesization has exactly the direct finite union as
its value. -/
theorem iteratedBinaryEvaluation_eq_finitePhysicalUnion
    {I : Type v} [Fintype I] (P : BinaryParenthesization I)
    (S : I → FiniteComponentState G Θ) (hS : NaryCompatible S)
    (U : FiniteComponentState G Θ)
    (hU : IteratedBinaryEvaluation P.shape
      (fun l ↦ S (P.leavesEquiv l)) U) :
    U = finitePhysicalUnion (⟨S, hS⟩ : NaryPhysicalDomain G Θ I) := by
  let hreindexed : NaryCompatible (fun l ↦ S (P.leavesEquiv l)) :=
    (naryCompatible_reindex P.leavesEquiv S).mpr hS
  calc
    U = naryUnion (fun l ↦ S (P.leavesEquiv l)) hreindexed :=
      hU.eq_naryUnion hreindexed
    _ = naryUnion S hS := by
      apply FiniteComponentState.ext
      exact narySupport_equiv P.leavesEquiv S
    _ = finitePhysicalUnion (⟨S, hS⟩ : NaryPhysicalDomain G Θ I) := rfl

/-- Any two valid parenthesizations of the same finite compatible family have
the same ambient-union value. -/
theorem iteratedBinaryEvaluation_parenthesization_independent
    {I : Type v} [Fintype I] (P Q : BinaryParenthesization I)
    (S : I → FiniteComponentState G Θ) (hS : NaryCompatible S)
    (U V : FiniteComponentState G Θ)
    (hU : IteratedBinaryEvaluation P.shape
      (fun l ↦ S (P.leavesEquiv l)) U)
    (hV : IteratedBinaryEvaluation Q.shape
      (fun l ↦ S (Q.leavesEquiv l)) V) :
    U = V := by
  rw [iteratedBinaryEvaluation_eq_finitePhysicalUnion P S hS U hU,
    iteratedBinaryEvaluation_eq_finitePhysicalUnion Q S hS V hV]

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

/-- A physical family over a state object `C` is the literal data of an
object of `Type / C`.  The branch type is universe-polymorphic, as it is in
the slice of all types over `C`. -/
structure PhysicalFamily (C : Type u) where
  /-- The branch type. -/
  left : Type v
  /-- The structure map to physical states. -/
  hom : left → C

/-- A physical family whose domain is finite. -/
structure FinitePhysicalFamily (C : Type u) where
  /-- The underlying object of `Type / C`. -/
  family : PhysicalFamily.{u, v} C
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
