module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.Composition
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The descent spine: core torsor, cofinal tail, exact target

This module is the coordinate-free composition of the two provider interfaces.
It contains no arithmetic; the arithmetic lives entirely inside the two
hypotheses, which are the manuscript's *finite core interface* and *cofinal
tail interface*.

* `CoreStage` — a finite family of admissible states of one common grade whose
  residues form a complete torsor under a finite subgroup `H ≤ ℚ/ℤ`, with a
  strictly positive barrier slack and a footprint the tail can avoid.
* `TailCovers` — for one grade `h`, a family of states beyond that footprint,
  all of grade `h` and mass at most `ε`, whose residues cover `G/H`.

Three universal lemmas then finish the descent.

*Torsor induction.*  Given the tail's freedom modulo `H` and the core's
complete `H`-torsor, the union realizes any prescribed residue in `τ + G`.
This is `exists_pair_residue_zero`, specialized to the residue `0`.

*Eventual torsor trivialization.*  Every element of `ℚ/ℤ` has finite order, so
it lies in `lowerPrimePowerStage Q` for every large `Q`
(`exists_mem_lowerPrimePowerStage`).  In particular the core class `τ`
eventually lies in the ambient group, which is exactly the hypothesis torsor
induction needs.

*Adjacent-lift uniqueness.*  `Erdos289.Support.value_eq_one_of_residue_zero`:
a centered state of mass in `(0,2)` has mass exactly `1`.

The mass bookkeeping is the manuscript's: `W ≤ (2 - s) + ε < 2` whenever the
tail load is below the core slack.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-! ### Eventual trivialization of the residue filtration -/

/--
Every centered residue is annihilated by its denominator, hence lies in every
sufficiently late bounded prime-power stage.  This is the exhaustiveness
`colim_Q G_Q = ℚ/ℤ` of the canonical filtration, in the form the descent uses.
-/
theorem exists_mem_lowerPrimePowerStage (x : TargetResidue) :
    ∃ n : ℕ, 0 < n ∧ ∀ Q, n < Q → x ∈ lowerPrimePowerStage Q := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) x
  refine ⟨q.den, q.den_pos, fun Q hQ => ?_⟩
  refine annihilatorStage_le_lower_of_lt q.den_pos hQ ?_
  show q.den • (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ)) q) = 0
  rw [← map_nsmul]
  refine (QuotientAddGroup.eq_zero_iff _).2 ?_
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨q.num, ?_⟩
  rw [zsmul_eq_mul, mul_one, nsmul_eq_mul]
  exact (Rat.den_mul_eq_num q).symm

/-! ### The finite core interface -/

/--
A finite homogeneous core stage: one common grade, a complete `H`-torsor of
residues, a strictly positive barrier slack, and a footprint.

The states are indexed by the group `H` itself, which is exactly what "complete
torsor" means: the residue of the state at `u` is `centre + u`.
-/
structure CoreStage (c : PhysicalConstraint) where
  /-- The finite residue subgroup the core torsor is modelled on. -/
  subgroup : AddSubgroup TargetResidue
  /-- The torsor class. -/
  centre : TargetResidue
  /-- The common grade of every core state. -/
  grade : ℕ
  /-- A footprint containing every core state. -/
  footprint : Support
  /-- The barrier slack `2 - sup W`. -/
  slack : ℚ
  slack_pos : 0 < slack
  /-- Completeness of the torsor: every class is realized, inside the footprint,
  at the common grade, with mass in `(0, 2 - slack]`. -/
  covers : ∀ u ∈ subgroup, ∃ S : Support,
    S ⊆ footprint ∧ S.Admissible smallBlockSizes c ∧ S.grade = grade ∧
      S.residue = centre + u ∧ 0 < S.value ∧ S.value ≤ 2 - slack

/-! ### The cofinal tail interface -/

/--
The tail interface at one grade: beyond the core footprint there are states of
grade exactly `h` and mass at most `ε`, whose residues cover every class of
`G/H`.

`G` is the ambient residue group of the tail (`G_X` in the manuscript) and `H`
is the core subgroup.
-/
def TailCovers (c : PhysicalConstraint) (F : Support) (H G : AddSubgroup TargetResidue)
    (h : ℕ) (ε : ℚ) : Prop :=
  ∀ v ∈ G, ∃ V : Support,
    V.Admissible smallBlockSizes (constraintBeyond c F) ∧
    V.grade = h ∧ V.residue - v ∈ H ∧ 0 ≤ V.value ∧ V.value ≤ ε

/-! ### Torsor induction -/

/--
Torsor induction, in the only instance the descent needs: if the core class
lies in the ambient tail group, the union of a core state and a tail state
realizes residue exactly zero, at grade `K + h` and mass below `2`.
-/
theorem exists_saturationWitness_of_tailCovers
    {c : PhysicalConstraint} (B : CoreStage c)
    {G : AddSubgroup TargetResidue} {h : ℕ} {ε : ℚ}
    (hcentre : B.centre ∈ G) (hε : ε < B.slack)
    (htail : TailCovers c B.footprint B.subgroup G h ε) :
    Nonempty (SaturationWitness 1 c (B.grade + h)) := by
  obtain ⟨V, hVadm, hVgrade, hVres, hVpos, hVle⟩ := htail (-B.centre) (G.neg_mem hcentre)
  -- the residual discrepancy lies in the core subgroup, so the torsor supplies it
  have huH : -(V.residue + B.centre) ∈ B.subgroup := by
    refine B.subgroup.neg_mem ?_
    have hV' := hVres
    rwa [sub_neg_eq_add] at hV'
  obtain ⟨S, hSsub, hSadm, hSgrade, hSres, hSpos, hSle⟩ := B.covers _ huH
  have hres : S.residue + V.residue = 0 := by
    rw [hSres]
    abel
  have hwitness :=
    saturationWitness_of_pairBeyond c (S := S) (F := B.footprint) (V := V)
      hSsub hSadm hVadm (by linarith) (by linarith) hres
  have hgrade : S.grade + V.grade = B.grade + h := by rw [hSgrade, hVgrade]
  exact ⟨hgrade ▸ hwitness⟩

/-! ### The final descent -/

/--
The manuscript's §8, verbatim: fix a core stage whose slack exceeds the tail
load, and let the tail supply every sufficiently large grade.  Then the exact
reciprocal grade spectrum at `1` is cofinite.
-/
theorem cofiniteSaturation_one_of_core_tail
    {c : PhysicalConstraint} (B : CoreStage c) {N : ℕ}
    (hsupply : ∀ h, N ≤ h → ∃ (G : AddSubgroup TargetResidue) (ε : ℚ),
      B.centre ∈ G ∧ ε < B.slack ∧ TailCovers c B.footprint B.subgroup G h ε) :
    CofiniteSaturation 1 c := by
  refine ⟨B.grade + N, fun k hk => ?_⟩
  obtain ⟨h, rfl⟩ : ∃ h, k = B.grade + h := ⟨k - B.grade, by omega⟩
  obtain ⟨G, ε, hcentre, hε, htail⟩ := hsupply h (by omega)
  exact exists_saturationWitness_of_tailCovers B hcentre hε htail

/-- Erdős 289 itself, from the two provider interfaces. -/
theorem erdos289Statement_of_core_tail
    (B : CoreStage originalConstraint) {N : ℕ}
    (hsupply : ∀ h, N ≤ h → ∃ (G : AddSubgroup TargetResidue) (ε : ℚ),
      B.centre ∈ G ∧ ε < B.slack ∧
        TailCovers originalConstraint B.footprint B.subgroup G h ε) :
    Erdos289Statement :=
  cofiniteSaturation_one_of_core_tail B hsupply

end Erdos289
