import Universal.FiniteComponentState

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Lattice

/-!
# Direct n-ary compatibility

For a finite family of admissible finite-component states, the canonical map
from the coproduct of the input component sets to the component set of their
ambient union is always surjective.  Direct compatibility is its isomorphism
locus.
-/

open scoped BigOperators

namespace Erdos289

set_option linter.style.haveILetI false

universe u v w

variable {G : Graphᵣ.{u}} {Θ : Set ℕ+} {I : Type v} [Fintype I]

private instance finitePiZero (H : Graphᵣ.{u}) [Finite H.carrier] :
    Finite (PiZeroObj H) :=
  Finite.of_surjective (piZeroMk H) fun c ↦ by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c
    exact ⟨x, rfl⟩

/-- The ambient union of the supports of a finite family of states. -/
def narySupport (S : I → FiniteComponentState G Θ) : Set G :=
  ⋃ i, (S i).support

theorem narySupport_finite (S : I → FiniteComponentState G Θ) :
    (narySupport S).Finite := by
  exact Set.finite_iUnion fun i ↦ (S i).support_finite

/-- Inclusion of one input induced graph into the induced graph on the ambient union. -/
def naryGraphInclusion (S : I → FiniteComponentState G Θ) (i : I) :
    (S i).graph ⟶ inducedGraph G (narySupport S) where
  toRelHom :=
    { toFun := fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨i, x.2⟩⟩
      map_rel' := fun h ↦ h }

/-- The canonical map from the coproduct of input components to union components. -/
def naryComponentMap (S : I → FiniteComponentState G Θ) :
    (Σ i, (S i).Components) → PiZeroObj (inducedGraph G (narySupport S))
  | ⟨i, c⟩ => piZeroMap (naryGraphInclusion S i) c

/-- Inclusion of the ambient union of a reindexed subfamily into the ambient
union of the original family. -/
def narySubfamilyGraphInclusion {J : Type w} (S : I → FiniteComponentState G Θ)
    (e : J ↪ I) :
    inducedGraph G (narySupport (fun j ↦ S (e j))) ⟶
      inducedGraph G (narySupport S) where
  toRelHom :=
    { toFun := fun x ↦ ⟨x.1, by
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 x.2
        exact Set.mem_iUnion.2 ⟨e j, hxj⟩⟩
      map_rel' := fun h ↦ h }

omit [Fintype I] in
theorem naryComponentMap_subfamily {J : Type w}
    (S : I → FiniteComponentState G Θ) (e : J ↪ I)
    (p : Σ j, (S (e j)).Components) :
    piZeroMap (narySubfamilyGraphInclusion S e)
        (naryComponentMap (fun j ↦ S (e j)) p) =
      naryComponentMap S ⟨e p.1, p.2⟩ := by
  obtain ⟨j, c⟩ := p
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  rfl

/-- Direct n-ary compatibility is the isomorphism locus of the canonical
component map. -/
def NaryCompatible (S : I → FiniteComponentState G Θ) : Prop :=
  Function.Bijective (naryComponentMap S)

omit [Fintype I] in
/-- Every union component contains a component coming from one input state. -/
theorem naryComponentMap_surjective (S : I → FiniteComponentState G Θ) :
    Function.Surjective (naryComponentMap S) := by
  intro c
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 x.2
  exact ⟨⟨i, piZeroMk (S i).graph ⟨x.1, hxi⟩⟩, rfl⟩

omit [Fintype I] in
/-- Direct compatibility is inherited by every reindexed subfamily. -/
theorem naryCompatible_subfamily {J : Type w}
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S)
    (e : J ↪ I) : NaryCompatible (fun j ↦ S (e j)) := by
  constructor
  · intro p q hpq
    have hmap := congrArg (piZeroMap (narySubfamilyGraphInclusion S e)) hpq
    rw [naryComponentMap_subfamily S e p, naryComponentMap_subfamily S e q] at hmap
    have hpq' := hS.1 hmap
    have hindex : p.1 = q.1 := e.injective (congrArg Sigma.fst hpq')
    cases p with
    | mk i c =>
      cases q with
      | mk j d =>
        dsimp at hindex
        subst j
        exact Sigma.ext rfl (Sigma.mk.inj_iff.mp hpq').2
  · exact naryComponentMap_surjective _

omit [Fintype I] in
/-- Compatibility forces distinct input supports to be disjoint. -/
theorem naryCompatible_pairwise_support_disjoint
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) :
    Pairwise fun i j ↦ Disjoint (S i).support (S j).support := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  have heq :
      naryComponentMap S ⟨i, piZeroMk (S i).graph ⟨x, hxi⟩⟩ =
        naryComponentMap S ⟨j, piZeroMk (S j).graph ⟨x, hxj⟩⟩ := rfl
  exact hij (congrArg Sigma.fst (hS.1 heq))

private def componentFiberMap (S : I → FiniteComponentState G Θ) (i : I)
    (c : (S i).Components) :
    ComponentFiber G (S i).support c →
      ComponentFiber G (narySupport S) (naryComponentMap S ⟨i, c⟩) :=
  fun x ↦ ⟨naryGraphInclusion S i x.1, by
    change piZeroMk (inducedGraph G (narySupport S)) (naryGraphInclusion S i x.1) =
      piZeroMap (naryGraphInclusion S i) c
    have hx := congrArg (piZeroMap (naryGraphInclusion S i)) x.2
    rw [piZeroMap_mk] at hx
    exact hx⟩

omit [Fintype I] in
private theorem componentFiberMap_bijective
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) (i : I)
    (c : (S i).Components) : Function.Bijective (componentFiberMap S i c) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z ↦ z.1.1) hxy
  · intro y
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 y.1.2
    let c' : (S j).Components := piZeroMk (S j).graph ⟨y.1.1, hxj⟩
    have hmap : naryComponentMap S ⟨j, c'⟩ = naryComponentMap S ⟨i, c⟩ := by
      change piZeroMap (naryGraphInclusion S j) c' =
        piZeroMap (naryGraphInclusion S i) c
      calc
        piZeroMap (naryGraphInclusion S j) c' =
            piZeroMk (inducedGraph G (narySupport S))
              (naryGraphInclusion S j ⟨y.1.1, hxj⟩) := rfl
        _ = piZeroMk (inducedGraph G (narySupport S)) y.1 := by
          congr 1
        _ = piZeroMap (naryGraphInclusion S i) c := by
          simpa only [naryComponentMap] using y.2
    have hp := hS.1 hmap
    have hji : j = i := congrArg Sigma.fst hp
    subst j
    have hc : c' = c := eq_of_heq (Sigma.mk.inj_iff.mp hp).2
    refine ⟨⟨⟨y.1.1, hxj⟩, hc⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl

private noncomputable def componentFiberEquiv
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) (i : I)
    (c : (S i).Components) :
    ComponentFiber G (S i).support c ≃
      ComponentFiber G (narySupport S) (naryComponentMap S ⟨i, c⟩) :=
  Equiv.ofBijective (componentFiberMap S i c) (componentFiberMap_bijective hS i c)

private theorem componentCardinality_naryComponentMap
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) (i : I)
    (c : (S i).Components) :
    componentCardinality G (narySupport S) (narySupport_finite S)
        (naryComponentMap S ⟨i, c⟩) =
      componentCardinality G (S i).support (S i).support_finite c := by
  letI : Finite (inducedGraph G (narySupport S)).carrier := narySupport_finite S
  letI : Finite (S i).graph.carrier := (S i).support_finite
  letI : Finite (ComponentFiber G (narySupport S) (naryComponentMap S ⟨i, c⟩)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (ComponentFiber G (S i).support c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ComponentFiber G (narySupport S) (naryComponentMap S ⟨i, c⟩)) :=
    Fintype.ofFinite _
  letI : Fintype (ComponentFiber G (S i).support c) := Fintype.ofFinite _
  apply Subtype.ext
  change Fintype.card
      (ComponentFiber G (narySupport S) (naryComponentMap S ⟨i, c⟩)) =
    Fintype.card (ComponentFiber G (S i).support c)
  exact Fintype.card_congr (componentFiberEquiv hS i c).symm

/-- On the compatible locus, every union component has an allowed size. -/
theorem naryCompatible_union_admissible
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) :
    ∀ c : PiZeroObj (inducedGraph G (narySupport S)),
      componentCardinality G (narySupport S) (narySupport_finite S) c ∈ Θ := by
  intro c
  obtain ⟨⟨i, d⟩, rfl⟩ := hS.2 c
  rw [componentCardinality_naryComponentMap hS]
  exact (S i).admissible d

/-- The admissible state carried by the ambient union on the direct compatible locus. -/
noncomputable def naryUnion (S : I → FiniteComponentState G Θ)
    (hS : NaryCompatible S) : FiniteComponentState G Θ where
  support := narySupport S
  support_finite := narySupport_finite S
  admissible := naryCompatible_union_admissible hS

private theorem componentType_naryUnion
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) (i : I)
    (c : (S i).Components) :
    (naryUnion S hS).componentType (naryComponentMap S ⟨i, c⟩) =
      (S i).componentType c := by
  apply Subtype.ext
  exact componentCardinality_naryComponentMap hS i c

/-- Component profiles add under a directly compatible finite union. -/
theorem componentProfile_naryUnion
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) :
    componentProfile (naryUnion S hS) = ∑ i, componentProfile (S i) := by
  classical
  letI (i : I) : Fintype (S i).Components := Fintype.ofFinite _
  letI : Finite (inducedGraph G (narySupport S)).carrier := narySupport_finite S
  letI : Fintype (PiZeroObj (inducedGraph G (narySupport S))) := Fintype.ofFinite _
  calc
    componentProfile (naryUnion S hS) =
        ∑ p : Σ i, (S i).Components,
          Finsupp.single ((naryUnion S hS).componentType (naryComponentMap S p)) 1 := by
      rw [componentProfile]
      change (∑ c : PiZeroObj (inducedGraph G (narySupport S)),
        Finsupp.single ((naryUnion S hS).componentType c) 1) = _
      exact (hS.sum_comp fun c ↦
        Finsupp.single ((naryUnion S hS).componentType c) 1).symm
    _ = ∑ p : Σ i, (S i).Components,
          Finsupp.single ((S p.1).componentType p.2) 1 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [componentType_naryUnion hS]
    _ = ∑ i, componentProfile (S i) := by
      simpa only [componentProfile] using
        (Fintype.sum_sigma' fun i c ↦ Finsupp.single ((S i).componentType c) 1)

/-- Fold a commutative-monoid valuation over the vertices of a finite state. -/
noncomputable def vertexFold {L : Type w} [AddCommMonoid L]
    (weight : G → L) (S : FiniteComponentState G Θ) : L := by
  classical
  letI : Finite S.support := S.support_finite
  letI : Fintype S.support := Fintype.ofFinite _
  exact ∑ x : S.support, weight x.1

private noncomputable def naryVertexEquiv
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) :
    (Σ i, (S i).support) ≃ (naryUnion S hS).support := by
  apply Equiv.ofBijective (fun p ↦ ⟨p.2.1, Set.mem_iUnion.2 ⟨p.1, p.2.2⟩⟩)
  constructor
  · intro p q hpq
    have hv : p.2.1 = q.2.1 := congrArg Subtype.val hpq
    have hi : p.1 = q.1 := by
      by_contra hij
      have hd := naryCompatible_pairwise_support_disjoint hS hij
      exact Set.disjoint_left.1 hd p.2.2 (hv ▸ q.2.2)
    cases p with
    | mk i x =>
      cases q with
      | mk j y =>
        dsimp at hi
        subst j
        cases Subtype.ext hv
        rfl
  · intro x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 x.2
    exact ⟨⟨i, ⟨x.1, hxi⟩⟩, Subtype.ext rfl⟩

/-- Every commutative-monoid vertex valuation is additive on compatible unions. -/
theorem vertexFold_naryUnion {L : Type w} [AddCommMonoid L]
    (weight : G → L) {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) :
    vertexFold weight (naryUnion S hS) = ∑ i, vertexFold weight (S i) := by
  classical
  letI (i : I) : Finite (S i).support := (S i).support_finite
  letI (i : I) : Fintype (S i).support := Fintype.ofFinite _
  letI : Finite (naryUnion S hS).support := (naryUnion S hS).support_finite
  letI : Fintype (naryUnion S hS).support := Fintype.ofFinite _
  rw [vertexFold]
  calc
    (∑ x : (naryUnion S hS).support, weight x.1) =
        ∑ p : Σ i, (S i).support, weight p.2.1 := by
      exact ((naryVertexEquiv hS).sum_comp fun x ↦ weight x.1).symm
    _ = ∑ i, vertexFold weight (S i) := by
      simpa only [vertexFold] using
        (Fintype.sum_sigma' fun (i : I) (x : (S i).support) ↦ weight (x : G))

/-- The ambient union equipped with an explicitly supplied admissibility
certificate.  This is the comparison state used in the maximality theorem. -/
noncomputable def naryUnionOfAdmissible (S : I → FiniteComponentState G Θ)
    (hadm : ∀ c : PiZeroObj (inducedGraph G (narySupport S)),
      componentCardinality G (narySupport S) (narySupport_finite S) c ∈ Θ) :
    FiniteComponentState G Θ where
  support := narySupport S
  support_finite := narySupport_finite S
  admissible := hadm

private noncomputable def componentCount {Θ' : Type u} : FCM Θ' →+ ℕ :=
  componentLabelLift fun _ ↦ 1

private theorem componentCount_profile {S : FiniteComponentState G Θ} :
    componentCount (componentProfile S) =
      @Fintype.card S.Components (Fintype.ofFinite _) := by
  classical
  simp [componentCount, componentProfile]

/-- The direct compatibility locus is maximal: admissibility of the ambient
union together with component-profile additivity forces the canonical
component map to be an isomorphism. -/
theorem naryCompatible_maximal (S : I → FiniteComponentState G Θ)
    (hadm : ∀ c : PiZeroObj (inducedGraph G (narySupport S)),
      componentCardinality G (narySupport S) (narySupport_finite S) c ∈ Θ)
    (hprofile : componentProfile (naryUnionOfAdmissible S hadm) =
      ∑ i, componentProfile (S i)) : NaryCompatible S := by
  classical
  let U := naryUnionOfAdmissible S hadm
  letI (i : I) : Fintype (S i).Components := Fintype.ofFinite _
  letI : Finite (inducedGraph G (narySupport S)).carrier := narySupport_finite S
  letI : Fintype (PiZeroObj (inducedGraph G (narySupport S))) := Fintype.ofFinite _
  letI : Fintype U.Components := Fintype.ofFinite _
  rw [NaryCompatible, Fintype.bijective_iff_surjective_and_card]
  refine ⟨naryComponentMap_surjective S, ?_⟩
  rw [Fintype.card_sigma]
  have hcount := congrArg componentCount hprofile
  have hcardU : Fintype.card U.Components = ∑ i, Fintype.card (S i).Components := by
    simpa [map_sum, componentCount_profile, U] using hcount
  calc
    (∑ i, Fintype.card (S i).Components) = Fintype.card U.Components := hcardU.symm
    _ = Fintype.card (PiZeroObj (inducedGraph G (narySupport S))) := by
      exact Fintype.card_congr (Equiv.refl _)

def IsAdmissibleSupport (G : Graphᵣ.{u}) (Θ : Set ℕ+) (A : Set G) : Prop :=
  ∀ hA : A.Finite, ∀ c : PiZeroObj (inducedGraph G A),
    componentCardinality G A hA c ∈ Θ

private theorem naryCompatible_support_admissible
    {S : I → FiniteComponentState G Θ} (hS : NaryCompatible S) :
    IsAdmissibleSupport G Θ (narySupport S) := by
  intro hA c
  simpa only using naryCompatible_union_admissible hS c

/-- Compatibility transfers to a finite family with the same ambient union
and the same total component profile. -/
theorem naryCompatible_of_support_profile_eq {J : Type w} [Fintype J]
    {S : I → FiniteComponentState G Θ}
    {T : J → FiniteComponentState G Θ} (hS : NaryCompatible S)
    (hsupport : narySupport T = narySupport S)
    (hprofile : (∑ i, componentProfile (T i)) =
      ∑ i, componentProfile (S i)) : NaryCompatible T := by
  have hadmAll : IsAdmissibleSupport G Θ (narySupport T) := by
    rw [hsupport]
    exact naryCompatible_support_admissible hS
  let hadm := hadmAll (narySupport_finite T)
  apply naryCompatible_maximal T hadm
  have hstates : naryUnionOfAdmissible T hadm = naryUnion S hS := by
    apply FiniteComponentState.ext
    exact hsupport
  rw [hstates, componentProfile_naryUnion hS, hprofile]

/-- Group a sum-indexed family into the two direct unions of its summands.
This construction is intrinsic to `naryUnion`; it does not choose a binary
physical multiplication or a parenthesization. -/
noncomputable def narySumGrouping {J : Type w} [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ)
    (hleft : NaryCompatible fun i ↦ S (.inl i))
    (hright : NaryCompatible fun j ↦ S (.inr j)) :
    Fin 2 → FiniteComponentState G Θ :=
  fun k ↦ if k = 0 then
    naryUnion (fun i ↦ S (.inl i)) hleft
  else
    naryUnion (fun j ↦ S (.inr j)) hright

@[simp]
theorem narySumGrouping_zero {J : Type w} [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ)
    (hleft : NaryCompatible fun i ↦ S (.inl i))
    (hright : NaryCompatible fun j ↦ S (.inr j)) :
    narySumGrouping S hleft hright 0 =
      naryUnion (fun i ↦ S (.inl i)) hleft := by
  simp [narySumGrouping]

@[simp]
theorem narySumGrouping_one {J : Type w} [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ)
    (hleft : NaryCompatible fun i ↦ S (.inl i))
    (hright : NaryCompatible fun j ↦ S (.inr j)) :
    narySumGrouping S hleft hright 1 =
      naryUnion (fun j ↦ S (.inr j)) hright := by
  simp [narySumGrouping]

/-- Grouping/flattening characterization of the direct finite multiplication
domain.  A sum-indexed family is directly compatible exactly when both
summands are directly compatible and their two direct unions are directly
compatible. -/
theorem naryCompatible_sum_iff_grouping {J : Type w} [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ) :
    NaryCompatible S ↔
      ∃ hleft : NaryCompatible (fun i ↦ S (.inl i)),
        ∃ hright : NaryCompatible (fun j ↦ S (.inr j)),
          NaryCompatible (narySumGrouping S hleft hright) := by
  constructor
  · intro hS
    let hleft : NaryCompatible (fun i ↦ S (.inl i)) :=
      naryCompatible_subfamily hS Function.Embedding.inl
    let hright : NaryCompatible (fun j ↦ S (.inr j)) :=
      naryCompatible_subfamily hS Function.Embedding.inr
    refine ⟨hleft, hright, ?_⟩
    apply naryCompatible_of_support_profile_eq hS
    · ext x
      simp [narySupport, narySumGrouping, naryUnion]
    · rw [Fin.sum_univ_two, Fintype.sum_sum_type]
      simp only [narySumGrouping_zero, narySumGrouping_one,
        componentProfile_naryUnion]
  · rintro ⟨hleft, hright, hgroup⟩
    apply naryCompatible_of_support_profile_eq hgroup
    · ext x
      simp [narySupport, narySumGrouping, naryUnion]
    · rw [Fintype.sum_sum_type, Fin.sum_univ_two]
      simp only [narySumGrouping_zero, narySumGrouping_one,
        componentProfile_naryUnion]

/-- Flattening a compatible two-block grouping gives exactly the same ambient
union as the original sum-indexed family.  This is the invariant core from
which parenthesization independence follows. -/
theorem naryUnion_sum_grouping {J : Type w} [Fintype J]
    (S : I ⊕ J → FiniteComponentState G Θ) (hS : NaryCompatible S)
    (hleft : NaryCompatible fun i ↦ S (.inl i))
    (hright : NaryCompatible fun j ↦ S (.inr j))
    (hgroup : NaryCompatible (narySumGrouping S hleft hright)) :
    naryUnion S hS = naryUnion (narySumGrouping S hleft hright) hgroup := by
  apply FiniteComponentState.ext
  ext x
  simp [naryUnion, narySupport, narySumGrouping]

end Erdos289
