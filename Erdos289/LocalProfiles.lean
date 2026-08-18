module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection.CyclicLadder
public import Erdos289.SimpleFiber
public import Erdos289.RestrictedFold
public import Erdos289.TransverseReservoir
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

/-!
# Intrinsic local simple-fibre profiles

A finite physical state system is consumed locally only through the image of
its joint observation/grade map.  The constructors below place the two local
mechanisms already proved in the project—fixed-cardinality additive folds and
monogenic cyclic orbits—behind that image interface.  Coordinates on a
one-dimensional prime fibre occur only as an additive equivalence used in the
proof of coverage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

universe u

/-- Bounded fibres give the canonical lower bound on a finite image. -/
theorem Finset.card_le_card_image_mul_of_fiber_bound
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset X) (f : X → Y) (m : ℕ)
    (hfiber : ∀ y ∈ A.image f, (A.filter fun x ↦ f x = y).card ≤ m) :
    A.card ≤ (A.image f).card * m := by
  let fibers : Y → Finset X := fun y ↦ A.filter fun x ↦ f x = y
  have hunion : (A.image f).biUnion fibers = A := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_biUnion.mp hx with ⟨y, -, hy⟩
      exact (Finset.mem_filter.mp hy).1
    · intro hx
      exact Finset.mem_biUnion.mpr ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  calc
    A.card = ((A.image f).biUnion fibers).card := congrArg Finset.card hunion.symm
    _ ≤ (A.image f).card * m :=
      Finset.card_biUnion_le_card_mul (A.image f) fibers m hfiber

/-- Image of the joint local observation/grade map. -/
def localProfile {X : Type u} {S : Type*}
    (observation : X → S) (grade : X → ℕ) : Set (S × ℕ) :=
  Set.range fun x ↦ (observation x, grade x)

/-- A local state system covers every simple-fibre point at one grade. -/
def CoversAtGrade {X : Type u} {S : Type*}
    (observation : X → S) (grade : X → ℕ) (h : ℕ) : Prop :=
  Set.univ ×ˢ {h} ⊆ localProfile observation grade

theorem coversAtGrade_iff {X : Type u} {S : Type*}
    (observation : X → S) (grade : X → ℕ) (h : ℕ) :
    CoversAtGrade observation grade h ↔
      ∀ s : S, ∃ x : X, observation x = s ∧ grade x = h := by
  constructor
  · intro hcover s
    have hs : (s, h) ∈ Set.univ ×ˢ ({h} : Set ℕ) :=
      ⟨Set.mem_univ s, by simp⟩
    rcases hcover hs with ⟨x, hx⟩
    exact ⟨x, Prod.mk.inj hx⟩
  · rintro hcover ⟨s, k⟩ ⟨-, hk⟩
    simp only [Set.mem_singleton_iff] at hk
    subst k
    rcases hcover s with ⟨x, hobs, hgrade⟩
    exact ⟨x, by simp [hobs, hgrade]⟩

namespace RestrictedFold

variable {G H : Type*} [AddCommMonoid G] [AddCommMonoid H]

/-- A fixed-cardinality fold is exactly a constant-grade local state system. -/
theorem coversAtGrade_iff_surjective (A : Finset G) (h : ℕ) :
    CoversAtGrade (fold A h) (fun _ ↦ h) h ↔ Surjective A h := by
  rw [coversAtGrade_iff]
  simp only [and_true]
  rfl

/-- Transport a canonical fixed-cardinality fold through an additive equivalence. -/
theorem surjective_map_iff (e : G ≃+ H) [DecidableEq G] [DecidableEq H]
    (A : Finset G) (h : ℕ) :
    Surjective (A.map e.toEquiv.toEmbedding) h ↔ Surjective A h := by
  constructor
  · intro hsurj x
    rcases hsurj (e x) with ⟨T, hT⟩
    let S : Finset G := T.1.map e.symm.toEquiv.toEmbedding
    have hSsub : S ⊆ A := by
      intro y hy
      rcases Finset.mem_map.mp hy with ⟨z, hz, hzy⟩
      rcases Finset.mem_map.mp (T.2.1 hz) with ⟨a, ha, haz⟩
      have hya : y = a := by
        rw [← hzy, ← haz]
        simp
      simpa [hya] using ha
    have hScard : S.card = h := by
      simpa [S] using T.2.2
    refine ⟨⟨S, hSsub, hScard⟩, ?_⟩
    change ∑ y ∈ S, y = x
    apply e.injective
    calc
      e (∑ y ∈ S, y) = ∑ y ∈ S, e y := by simp
      _ = ∑ z ∈ T.1, z := by simp [S]
      _ = e x := hT
  · intro hsurj y
    rcases hsurj (e.symm y) with ⟨S, hS⟩
    have hS' : ∑ z ∈ S.1, z = e.symm y := by
      exact hS
    let T : Finset H := S.1.map e.toEquiv.toEmbedding
    have hTsub : T ⊆ A.map e.toEquiv.toEmbedding := by
      exact (Finset.map_subset_map (f := e.toEquiv.toEmbedding)).2 S.2.1
    have hTcard : T.card = h := by
      simpa [T] using S.2.2
    refine ⟨⟨T, hTsub, hTcard⟩, ?_⟩
    change ∑ z ∈ T, z = y
    calc
      ∑ z ∈ T, z = ∑ z ∈ S.1, e z := by simp [T]
      _ = e (∑ z ∈ S.1, z) := by simp
      _ = e (e.symm y) := by rw [hS']
      _ = y := e.apply_symm_apply y

section PrimeFiber

variable {p : ℕ} [Fact p.Prime]
variable {S : Type*} [AddCommGroup S]

/--
Coordinate-free DdS coverage for a one-dimensional prime fibre.  The
equivalence is a proof coordinate; the conclusion is the intrinsic joint-image
condition on `S`.
-/
theorem coversAtGrade_of_card_bound
    (e : S ≃+ ZMod p) [DecidableEq S]
    (A : Finset S) (h : ℕ)
    (hA : A.Nonempty) (hh : h ≤ A.card)
    (hfull : p ≤ h * (A.card - h) + 1) :
    CoversAtGrade (fold A h) (fun _ ↦ h) h := by
  rw [coversAtGrade_iff_surjective]
  rw [← surjective_map_iff e A h]
  apply surjective_of_card_bound
  · exact hA.map
  · simpa using hh
  · simpa using hfull

end PrimeFiber

/-- DdS coverage specialized to the canonical prime-power simple fibre. -/
theorem coversAtGrade_primePowerSimpleFiber
    {Q p e h : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (A : Finset (PrimePowerSimpleFiber Q))
    (hA : A.Nonempty) (hh : h ≤ A.card)
    (hfull : p ≤ h * (A.card - h) + 1) :
    CoversAtGrade (fold A h) (fun _ ↦ h) h := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  exact coversAtGrade_of_card_bound
    (primePowerSimpleFiberAddEquiv hp he hQ) A h hA hh hfull

end RestrictedFold

namespace CyclicLadder

variable {S : Type*} [AddGroup S]

/-- A covering monogenic orbit is a homogeneous local profile. -/
theorem coversAtGrade_of_generatesIn
    {c : S} {N h : ℕ} (hc : AffineCorrection.CyclicLadder.GeneratesIn c N) :
    CoversAtGrade (AffineCorrection.CyclicLadder.orbit c N) (fun _ ↦ h) h := by
  rw [coversAtGrade_iff]
  intro s
  rcases hc s with ⟨j, hj⟩
  exact ⟨j, hj, rfl⟩

/-- Every nonzero point of a prime simple fibre gives a homogeneous full cover. -/
theorem coversAtGrade_zmod
    {p h : ℕ} (hp : p.Prime) (c : ZMod p) (hc : c ≠ 0) :
    CoversAtGrade (AffineCorrection.CyclicLadder.orbit c (p - 1)) (fun _ ↦ h) h :=
  coversAtGrade_of_generatesIn
    (AffineCorrection.CyclicLadder.zmod_generatesIn_pred hp c hc)

/-- Coordinate-free form: every nonzero point in a one-dimensional prime
fibre yields a homogeneous cyclic cover. -/
theorem coversAtGrade_primeFiber
    {p h : ℕ} {S : Type*} [AddCommGroup S]
    (hp : p.Prime) (e : S ≃+ ZMod p) (c : S) (hc : c ≠ 0) :
    CoversAtGrade (AffineCorrection.CyclicLadder.orbit c (p - 1))
      (fun _ ↦ h) h := by
  apply coversAtGrade_of_generatesIn
  intro s
  have hec : e c ≠ 0 := by
    intro hec0
    exact hc (e.injective (by simpa using hec0))
  rcases AffineCorrection.CyclicLadder.zmod_generatesIn_pred hp (e c) hec (e s) with
    ⟨j, hj⟩
  refine ⟨j, e.injective ?_⟩
  change e (j.1 • c) = e s
  rw [map_nsmul]
  exact hj

/-- Cyclic coverage specialized to the canonical prime-power simple fibre. -/
theorem coversAtGrade_primePowerSimpleFiber
    {Q p e h : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (c : PrimePowerSimpleFiber Q) (hc : c ≠ 0) :
    CoversAtGrade (AffineCorrection.CyclicLadder.orbit c (p - 1))
      (fun _ ↦ h) h :=
  coversAtGrade_primeFiber hp (primePowerSimpleFiberAddEquiv hp he hQ) c hc

end CyclicLadder

namespace TransverseReservoir

/-- A sufficiently large intrinsic reservoir image supplies a homogeneous DdS
profile without exposing arithmetic labels. -/
theorem restrictedFold_coversAtGrade
    {Q p e h : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) (hne : R.simpleValues.Nonempty)
    (hh : h ≤ R.simpleValues.card)
    (hfull : p ≤ h * (R.simpleValues.card - h) + 1) :
    CoversAtGrade (RestrictedFold.fold R.simpleValues h) (fun _ ↦ h) h :=
  RestrictedFold.coversAtGrade_primePowerSimpleFiber
    hp he hQ R.simpleValues hne hh hfull

/-- Any one reservoir atom supplies the nonzero step for a homogeneous cyclic
simple-fibre profile. -/
theorem atom_cyclic_coversAtGrade
    {Q p e h : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) {S : Support} (hS : S ∈ R.atoms) :
    CoversAtGrade
      (AffineCorrection.CyclicLadder.orbit
        (S.transverseClass (R.transverse S hS)) (p - 1))
      (fun _ ↦ h) h :=
  CyclicLadder.coversAtGrade_primePowerSimpleFiber hp he hQ _
    (Support.transverseClass_ne_zero (R.transverse S hS))

end TransverseReservoir

namespace QuantitativeTransverseReservoir

/-- The intrinsic row-size and fibre-multiplicity bounds force a large image
in the canonical simple quotient. -/
theorem rowMin_le_simpleValues_card_mul
    {Q rowMin fiberMultiplicity conflictDegree : ℕ}
    {c : PhysicalConstraint} {maxMass : ℚ}
    (R : QuantitativeTransverseReservoir Q c rowMin fiberMultiplicity
      conflictDegree maxMass) :
    rowMin ≤ R.toTransverseReservoir.simpleValues.card * fiberMultiplicity := by
  classical
  calc
    rowMin ≤ R.atoms.card := R.row_card
    _ = R.atoms.attach.card := by simp
    _ ≤ R.toTransverseReservoir.simpleValues.card * fiberMultiplicity := by
      apply Finset.card_le_card_image_mul_of_fiber_bound
      intro x hx
      simpa [TransverseReservoir.simpleValues,
        TransverseReservoir.simpleValueFiber] using R.fiber_card x

end QuantitativeTransverseReservoir

end Erdos289
