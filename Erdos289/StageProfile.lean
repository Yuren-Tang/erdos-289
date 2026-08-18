module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.GradeInterval
public import Erdos289.Composition
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# What one prime-power stage contributes

This is the bridge between the arithmetic of a stage and the tail interface:
a compatible transverse pool at a prime-power current, whose image in the
associated simple fibre is large, realizes *every* class of that fibre at
*every* grade of an interval, with mass proportional to the grade.

The ingredients are proved elsewhere and only combined here.

* the aggregate of a pairwise-compatible family has additive value, grade and
  residue (`Erdos289.aggregateSupport_value`, `_grade`, `_residue`);
* the simple-fibre class is additive over such a family, because it is a
  quotient homomorphism applied to the additive residue
  (`Erdos289.aggregateSupport_stageClass`);
* the restricted fold over the pool's fibre image is surjective at every grade
  of the Dias da Silva–Hamidoune interval
  (`Erdos289.TransverseReservoir.restrictedFold_coversAtGrade_of_mem_Icc`).

Choosing one atom per retained fibre value turns a fold witness into a
subfamily of the pool, and the three additivity statements turn that subfamily
into a state of the prescribed grade, mass and class.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/-! ### A total form of the simple-fibre class -/

open Classical in
/-- The residue of a support, lifted to the current stage subgroup; zero when
the support does not factor through the stage. -/
noncomputable def Support.stageLift (S : Support) (Q : ℕ) : primePowerStage Q :=
  if hS : S.FactorsThroughPrimePowerStage Q then ⟨S.residue, hS⟩ else 0

theorem Support.stageLift_val {S : Support} {Q : ℕ}
    (hS : S.FactorsThroughPrimePowerStage Q) :
    ((S.stageLift Q : primePowerStage Q) : TargetResidue) = S.residue := by
  rw [stageLift, dif_pos hS]

/-- The simple-fibre class as a total function. -/
noncomputable def Support.stageClass (S : Support) (Q : ℕ) : PrimePowerSimpleFiber Q :=
  QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) (S.stageLift Q)

theorem Support.stageClass_eq {S : Support} {Q : ℕ}
    (hS : S.FactorsThroughPrimePowerStage Q) :
    S.stageClass Q = S.simpleFiberClass hS := by
  rw [stageClass, simpleFiberClass, stageLift, dif_pos hS]

theorem Support.stageClass_eq_transverseClass {S : Support} {Q : ℕ}
    (hS : S.FilteredTransverse Q) :
    S.stageClass Q = S.transverseClass hS :=
  Support.stageClass_eq _

/-! ### Additivity over a compatible pool -/

theorem aggregateSupport_factorsThrough
    {Q : ℕ} {c : PhysicalConstraint} {A : Finset Support}
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c)
    (hfac : ∀ S ∈ A, S.FactorsThroughPrimePowerStage Q) :
    (aggregateSupport A).FactorsThroughPrimePowerStage Q := by
  classical
  change (aggregateSupport A).residue ∈ primePowerStage Q
  rw [aggregateSupport_residue hpair]
  exact AddSubgroup.sum_mem _ fun S hS => hfac S hS

theorem aggregateSupport_stageClass
    {Q : ℕ} {c : PhysicalConstraint} {A : Finset Support}
    (hpair : (A : Set Support).Pairwise fun S T ↦ S.CompatibleFor T c)
    (hfac : ∀ S ∈ A, S.FactorsThroughPrimePowerStage Q) :
    (aggregateSupport A).stageClass Q = ∑ S ∈ A, S.stageClass Q := by
  classical
  have hlift : (aggregateSupport A).stageLift Q = ∑ S ∈ A, S.stageLift Q := by
    refine Subtype.ext ?_
    rw [AddSubgroup.val_finsetSum,
      Support.stageLift_val (aggregateSupport_factorsThrough hpair hfac),
      aggregateSupport_residue hpair]
    exact Finset.sum_congr rfl fun S hS => (Support.stageLift_val (hfac S hS)).symm
  rw [Support.stageClass, hlift, map_sum]
  rfl

/-- Two elements of the current stage have the same simple-fibre class exactly
when they differ by an element of the lower stage. -/
theorem stageClass_eq_iff_sub_mem {Q : ℕ} {y z : TargetResidue}
    (hy : y ∈ primePowerStage Q) (hz : z ∈ primePowerStage Q) :
    QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) (⟨y, hy⟩ : primePowerStage Q)
        = QuotientAddGroup.mk' (lowerInsidePrimePowerStage Q) (⟨z, hz⟩ : primePowerStage Q)
      ↔ y - z ∈ lowerPrimePowerStage Q := by
  rw [QuotientAddGroup.mk'_eq_mk']
  constructor
  · rintro ⟨u, hu, huz⟩
    have hval : (u : TargetResidue) = z - y := by
      have hcoe := congrArg Subtype.val huz
      simp only [AddSubgroup.coe_add] at hcoe
      rw [← hcoe]
      abel
    have hzy : z - y ∈ lowerPrimePowerStage Q := by
      have hmem : (u : TargetResidue) ∈ lowerPrimePowerStage Q := hu
      rwa [hval] at hmem
    have hneg := (lowerPrimePowerStage Q).neg_mem hzy
    rwa [neg_sub] at hneg
  · intro hsub
    have hzy : z - y ∈ lowerPrimePowerStage Q := by
      have hneg := (lowerPrimePowerStage Q).neg_mem hsub
      rwa [neg_sub] at hneg
    refine ⟨⟨z - y, AddSubgroup.sub_mem _ hz hy⟩, hzy, ?_⟩
    refine Subtype.ext ?_
    simp only [AddSubgroup.coe_add]
    abel

/-- Two supports factoring through the current stage have the same class
exactly when their residues differ by an element of the lower stage. -/
theorem Support.stageClass_eq_iff {Q : ℕ} {S T : Support}
    (hS : S.FactorsThroughPrimePowerStage Q) (hT : T.FactorsThroughPrimePowerStage Q) :
    S.stageClass Q = T.stageClass Q ↔ S.residue - T.residue ∈ lowerPrimePowerStage Q := by
  rw [Support.stageClass_eq hS, Support.stageClass_eq hT]
  exact stageClass_eq_iff_sub_mem hS hT

/-- A reservoir whose atoms have pairwise distinct simple-fibre classes has an
image in the fibre as large as itself. -/
theorem TransverseReservoir.card_simpleValues_of_injective
    {Q : ℕ} {c : PhysicalConstraint} (R : TransverseReservoir Q c)
    (hinj : ∀ S ∈ R.atoms, ∀ T ∈ R.atoms, S.stageClass Q = T.stageClass Q → S = T) :
    R.simpleValues.card = R.atoms.card := by
  classical
  have hkey : R.simpleValues
      = R.atoms.attach.image fun S => S.1.transverseClass (R.transverse S.1 S.2) := rfl
  rw [hkey, Finset.card_image_of_injOn, Finset.card_attach]
  intro S _ T _ hST
  refine Subtype.ext (hinj S.1 S.2 T.1 T.2 ?_)
  rw [Support.stageClass_eq_transverseClass (R.transverse S.1 S.2),
    Support.stageClass_eq_transverseClass (R.transverse T.1 T.2)]
  exact hST

/-! ### One stage realizes every class at every grade of its interval -/

/--
The local epimorphism of one prime-power stage.

`P` is a compatible transverse pool at the current `Q = p ^ e`.  If its image
in the simple fibre has `m` points and the Dias da Silva–Hamidoune condition
holds at the endpoint `a`, then for every grade `h ∈ [a, m - a]` and every
class `x` of the fibre there is a subfamily of `P` of exactly `h` atoms whose
aggregate has grade `h`, mass at most `h · maxMass`, and simple-fibre class
exactly `x`.
-/
theorem exists_pool_state_of_class
    {Q p e : ℕ} {c : PhysicalConstraint} (P : CompatibleTransversePool Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    {a h : ℕ} (hh : 0 < h) (hah : a ≤ h)
    (hhm : h + a ≤ P.toTransverseReservoir.simpleValues.card)
    (hend : p ≤ a * (P.toTransverseReservoir.simpleValues.card - a) + 1)
    {maxMass : ℚ} (hmass : ∀ S ∈ P.atoms, S.value ≤ maxMass)
    (hgrade : ∀ S ∈ P.atoms, S.grade = 1)
    (x : PrimePowerSimpleFiber Q) :
    ∃ A : Finset Support, A ⊆ P.atoms ∧ A.card = h ∧
      (A : Set Support).Pairwise (fun S T ↦ S.CompatibleFor T c) ∧
      (aggregateSupport A).grade = h ∧
      (aggregateSupport A).value ≤ h * maxMass ∧
      (aggregateSupport A).stageClass Q = x := by
  classical
  have hne : P.toTransverseReservoir.simpleValues.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hcov :=
    TransverseReservoir.restrictedFold_coversAtGrade_of_mem_Icc
      P.toTransverseReservoir hp he hQ hne hah hhm hend
  rw [coversAtGrade_iff] at hcov
  obtain ⟨⟨Tset, hTsub, hTcard⟩, hTfold, -⟩ := hcov x
  have hTsum : ∑ v ∈ Tset, v = x := hTfold
  -- one atom per retained fibre value
  have hex : ∀ v : {v // v ∈ P.toTransverseReservoir.simpleValues},
      ∃ S : {S // S ∈ P.atoms},
        S.1.transverseClass (P.transverse S.1 S.2) = v.1 := by
    intro v
    exact (TransverseReservoir.mem_simpleValues_iff _ _).1 v.2
  set sec : {v // v ∈ P.toTransverseReservoir.simpleValues} → {S // S ∈ P.atoms} :=
    fun v => (hex v).choose with hsecdef
  have hsecClass : ∀ v, (sec v).1.stageClass Q = v.1 := by
    intro v
    rw [Support.stageClass_eq_transverseClass (P.transverse (sec v).1 (sec v).2)]
    exact (hex v).choose_spec
  set g : {v // v ∈ Tset} → Support := fun w => (sec ⟨w.1, hTsub w.2⟩).1 with hgdef
  have hgmem : ∀ w, g w ∈ P.atoms := fun w => (sec ⟨w.1, hTsub w.2⟩).2
  have hgclass : ∀ w : {v // v ∈ Tset}, (g w).stageClass Q = w.1 :=
    fun w => hsecClass ⟨w.1, hTsub w.2⟩
  have hginj : Function.Injective g := by
    intro w w' hww
    refine Subtype.ext ?_
    have h1 := hgclass w
    have h2 := hgclass w'
    rw [hww, h2] at h1
    exact h1.symm
  set A : Finset Support := Tset.attach.image g with hAdef
  have hAsub : A ⊆ P.atoms := by
    intro S hS
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hS
    exact hgmem w
  have hApair : (A : Set Support).Pairwise (fun S T ↦ S.CompatibleFor T c) :=
    P.compatible.mono (by intro S hS; exact hAsub hS)
  have hAcard : A.card = h := by
    rw [hAdef, Finset.card_image_of_injective _ hginj, Finset.card_attach, hTcard]
  have hreindex : ∀ F : Support → PrimePowerSimpleFiber Q,
      ∑ S ∈ A, F S = ∑ w ∈ Tset.attach, F (g w) := by
    intro F
    rw [hAdef]
    exact Finset.sum_image fun a _ b _ hab => hginj hab
  refine ⟨A, hAsub, hAcard, hApair, ?_, ?_, ?_⟩
  · rw [aggregateSupport_grade hApair]
    calc ∑ S ∈ A, S.grade = ∑ S ∈ A, 1 := Finset.sum_congr rfl fun S hS => hgrade S (hAsub hS)
      _ = A.card := by simp
      _ = h := hAcard
  · rw [aggregateSupport_value hApair]
    calc ∑ S ∈ A, S.value ≤ ∑ _S ∈ A, maxMass :=
          Finset.sum_le_sum fun S hS => hmass S (hAsub hS)
      _ = A.card * maxMass := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = h * maxMass := by rw [hAcard]
  · rw [aggregateSupport_stageClass hApair
      (fun S hS => Classical.choose (P.transverse S (hAsub hS))), hreindex]
    calc ∑ w ∈ Tset.attach, (g w).stageClass Q = ∑ w ∈ Tset.attach, (w : PrimePowerSimpleFiber Q) :=
          Finset.sum_congr rfl fun w _ => hgclass w
      _ = ∑ v ∈ Tset, v := Finset.sum_attach Tset id
      _ = x := hTsum

end Erdos289
