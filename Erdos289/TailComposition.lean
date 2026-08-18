module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.Descent

@[expose] public section

/-!
# Composing tail stages along the residue filtration

`Erdos289.TailCovers` asks a single family to cover `G/H`.  The provider builds
it one simple jump at a time: stage `i` covers `G_{i+1}/G_i` and lives beyond
everything already placed.  Composing two consecutive stages is torsor
induction again — the same argument as `exists_saturationWitness_of_tailCovers`,
one level down — and iterating it along a chain from `H` to `G` is a plain
induction.

`TailStage` is `TailCovers` with the extra datum the composition needs: a finite
footprint containing the stage's states, so that the next stage can be required
to live beyond it.  Grades and loads add.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

theorem Support.admissible_empty (L : Set ℕ) (c : PhysicalConstraint) :
    (∅ : Support).Admissible L c := by
  simp [Support.Admissible, Support.HasBlockSizes, Support.Avoids, Support.Separated]

@[simp]
theorem Support.residue_empty : (∅ : Support).residue = 0 := by
  rw [Support.residue, Support.value_empty]
  exact map_zero _

/--
One stage of the tail: states of grade exactly `h` and mass at most `ε`, all
inside the finite footprint `F`, whose residues cover `G` modulo `H`.
-/
def TailStage (c : PhysicalConstraint) (F : Support)
    (H G : AddSubgroup TargetResidue) (h : ℕ) (ε : ℚ) : Prop :=
  ∀ v ∈ G, ∃ V : Support, V ⊆ F ∧
    V.Admissible smallBlockSizes c ∧
    V.grade = h ∧ V.residue - v ∈ H ∧ 0 ≤ V.value ∧ V.value ≤ ε

/-- The empty stage covers `H` modulo itself at grade zero and zero cost. -/
theorem tailStage_empty (c : PhysicalConstraint) (H : AddSubgroup TargetResidue) :
    TailStage c ∅ H H 0 0 := by
  intro v hv
  refine ⟨∅, Finset.Subset.refl _, Support.admissible_empty _ _, ?_, ?_, ?_, ?_⟩
  · simp [Support.grade]
  · simpa using H.neg_mem hv
  · simp [Support.value]
  · simp [Support.value]

/--
Torsor induction one level down: a stage covering `G₁/H` and a stage beyond its
footprint covering `G₂/G₁` compose to a stage covering `G₂/H`, with grades and
loads added.
-/
theorem TailStage.comp
    {c : PhysicalConstraint} {F₁ F₂ : Support}
    {H G₁ G₂ : AddSubgroup TargetResidue} {h₁ h₂ : ℕ} {ε₁ ε₂ : ℚ}
    (s₁ : TailStage c F₁ H G₁ h₁ ε₁)
    (s₂ : TailStage (constraintBeyond c F₁) F₂ G₁ G₂ h₂ ε₂) :
    TailStage c (F₁ ∪ F₂) H G₂ (h₁ + h₂) (ε₁ + ε₂) := by
  intro v hv
  obtain ⟨V₂, hV₂sub, hV₂adm, hV₂grade, hV₂res, hV₂pos, hV₂le⟩ := s₂ v hv
  -- the discrepancy of the upper stage is served by the lower one
  obtain ⟨V₁, hV₁sub, hV₁adm, hV₁grade, hV₁res, hV₁pos, hV₁le⟩ :=
    s₁ (-(V₂.residue - v)) (G₁.neg_mem hV₂res)
  refine ⟨V₁ ∪ V₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.union_subset_union hV₁sub hV₂sub
  · exact admissible_union_of_pairBeyond c hV₁sub hV₁adm hV₂adm
  · rw [grade_union_of_pairBeyond c hV₁sub hV₂adm.2.1, hV₁grade, hV₂grade]
  · rw [residue_union_of_pairBeyond c hV₁sub hV₂adm.2.1]
    have : V₁.residue + V₂.residue - v = V₁.residue - -(V₂.residue - v) := by abel
    rw [this]
    exact hV₁res
  · rw [Support.value_union
      (support_disjoint_of_avoids_beyond c hV₂adm.2.1 |>.mono_left hV₁sub)]
    linarith
  · rw [Support.value_union
      (support_disjoint_of_avoids_beyond c hV₂adm.2.1 |>.mono_left hV₁sub)]
    linarith

/--
A chain of stages, each beyond the accumulated footprint of its predecessors,
covers the top group modulo the bottom one.
-/
theorem tailStage_chain
    (b : PhysicalConstraint) (H : AddSubgroup TargetResidue)
    (G : ℕ → AddSubgroup TargetResidue) (F : ℕ → Support)
    (gr : ℕ → ℕ) (cost : ℕ → ℚ) (hG0 : G 0 = H)
    (hstage : ∀ i, TailStage (constraintBeyond b ((Finset.range i).biUnion F))
      (F i) (G i) (G (i + 1)) (gr i) (cost i)) :
    ∀ n, TailStage b ((Finset.range n).biUnion F) H (G n)
      (∑ i ∈ Finset.range n, gr i) (∑ i ∈ Finset.range n, cost i) := by
  intro n
  induction n with
  | zero =>
      simpa [hG0] using tailStage_empty b H
  | succ n ih =>
      have hcomp := ih.comp (hstage n)
      have hfoot : ((Finset.range n).biUnion F) ∪ F n
          = (Finset.range (n + 1)).biUnion F := by
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
        constructor
        · rintro (⟨i, hi, hx⟩ | hx)
          · exact ⟨i, by omega, hx⟩
          · exact ⟨n, by omega, hx⟩
        · rintro ⟨i, hi, hx⟩
          by_cases hin : i = n
          · subst hin
            exact Or.inr hx
          · exact Or.inl ⟨i, by omega, hx⟩
      rw [hfoot] at hcomp
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact hcomp

/-- Forgetting the footprint turns a stage into the tail interface. -/
theorem tailCovers_of_tailStage
    {c : PhysicalConstraint} {F F' : Support}
    {H G : AddSubgroup TargetResidue} {h : ℕ} {ε : ℚ}
    (s : TailStage (constraintBeyond c F) F' H G h ε) :
    TailCovers c F H G h ε := by
  intro v hv
  obtain ⟨V, -, hadm, hgrade, hres, hpos, hle⟩ := s v hv
  exact ⟨V, hadm, hgrade, hres, hpos, hle⟩

end Erdos289
