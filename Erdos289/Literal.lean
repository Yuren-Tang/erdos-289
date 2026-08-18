module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.Statement
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# The literal form of Erdős problem 289

`Erdos289.Erdos289Statement` is phrased through the intrinsic objects of this
development: a finite support in the positive-integer path, its connected
components, and the exact reciprocal value.  Nothing in that phrasing mentions
intervals, because an interval decomposition is a presentation of a support and
not an invariant of it.

This module proves that the two phrasings agree.  The mathematical content is
one lemma: a connected component of the graph induced by a finite set of
positive integers on the path is *convex*, hence an integer interval.  Given
that, a support of grade `k` is literally a family of `k` pairwise disjoint,
pairwise non-adjacent integer intervals, and the intrinsic statement unfolds to
the sentence printed on erdosproblems.com.

## Main statements

* `Erdos289.Erdos289Literal` — the form used by the `erdos_289` entry of
  `google-deepmind/formal-conjectures`.
* `Erdos289.Erdos289LiteralSeparated` — the form displayed on
  erdosproblems.com/289, which additionally requires the intervals to be
  non-adjacent.
* `Erdos289.erdos289Literal_of_statement` and
  `Erdos289.erdos289LiteralSeparated_of_statement` — both follow from
  `Erdos289Statement`.

## References

* [erdosproblems.com/289](https://www.erdosproblems.com/289)
* `FormalConjectures/ErdosProblems/289.lean` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/-! ## Components of a finite support are convex -/

section Convexity

variable {S : Support}

/--
Walking inside a finite support can only move by one, so a walk from `x` to `y`
cannot step over any denominator between them: every such denominator is itself
a support point, reachable from `x`.
-/
private theorem reachable_of_walk_between :
    ∀ {x y : {n : Denominator // n ∈ S}}, S.graph.Walk x y →
      ∀ z : Denominator, min (x.1 : ℕ) (y.1 : ℕ) ≤ (z : ℕ) →
        (z : ℕ) ≤ max (x.1 : ℕ) (y.1 : ℕ) →
        ∃ hz : z ∈ S, S.graph.Reachable x ⟨z, hz⟩ := by
  intro x y w
  induction w with
  | @nil u =>
      intro z h1 h2
      simp only [min_self, max_self] at h1 h2
      have hz : z = u.1 := PNat.coe_injective (by omega)
      subst hz
      exact ⟨u.2, SimpleGraph.Reachable.refl _⟩
  | @cons u v t hadj p ih =>
      intro z h1 h2
      by_cases hzu : (z : ℕ) = (u.1 : ℕ)
      · have : z = u.1 := PNat.coe_injective hzu
        subst this
        exact ⟨u.2, SimpleGraph.Reachable.refl _⟩
      · have hstep : (u.1 : ℕ) + 1 = (v.1 : ℕ) ∨ (v.1 : ℕ) + 1 = (u.1 : ℕ) := hadj
        have h1' : min (v.1 : ℕ) (t.1 : ℕ) ≤ (z : ℕ) := by omega
        have h2' : (z : ℕ) ≤ max (v.1 : ℕ) (t.1 : ℕ) := by omega
        obtain ⟨hz, hreach⟩ := ih z h1' h2'
        exact ⟨hz, (SimpleGraph.Adj.reachable hadj).trans hreach⟩

/--
Convexity of connected components: if two support points lie in the same
component, so does every denominator between them.
-/
theorem Support.mem_of_between {x y : Denominator} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : S.graph.connectedComponentMk ⟨x, hx⟩ = S.graph.connectedComponentMk ⟨y, hy⟩)
    {z : Denominator} (h1 : min (x : ℕ) (y : ℕ) ≤ (z : ℕ))
    (h2 : (z : ℕ) ≤ max (x : ℕ) (y : ℕ)) :
    ∃ hz : z ∈ S,
      S.graph.connectedComponentMk ⟨z, hz⟩ = S.graph.connectedComponentMk ⟨x, hx⟩ := by
  obtain ⟨w⟩ := SimpleGraph.ConnectedComponent.exact hxy
  obtain ⟨hz, hreach⟩ := reachable_of_walk_between w z h1 h2
  exact ⟨hz, (SimpleGraph.ConnectedComponent.sound hreach).symm⟩

end Convexity

/-! ## The interval carried by one component -/

section Blocks

variable {S : Support}

/-- The denominators of one connected component, as a finite set of naturals. -/
noncomputable def Support.blockNat (c : S.Blocks) : Finset ℕ := by
  classical
  exact (Finset.univ.filter
      fun x : {n : Denominator // n ∈ S} => S.graph.connectedComponentMk x = c).image
    fun x => (x.1 : ℕ)

theorem Support.mem_blockNat_iff (c : S.Blocks) (n : Denominator) :
    (n : ℕ) ∈ S.blockNat c ↔
      ∃ hn : n ∈ S, S.graph.connectedComponentMk ⟨n, hn⟩ = c := by
  classical
  simp only [Support.blockNat, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, hval⟩
    have : x.1 = n := PNat.coe_injective hval
    subst this
    exact ⟨x.2, hx⟩
  · rintro ⟨hn, hc⟩
    exact ⟨⟨n, hn⟩, hc, rfl⟩

theorem Support.pos_of_mem_blockNat {c : S.Blocks} {m : ℕ} (hm : m ∈ S.blockNat c) :
    0 < m := by
  classical
  simp only [Support.blockNat, Finset.mem_image, Finset.mem_filter] at hm
  obtain ⟨x, -, rfl⟩ := hm
  exact x.1.2

theorem Support.blockNat_card (c : S.Blocks) : (S.blockNat c).card = S.blockSize c := by
  classical
  have hinj : Function.Injective
      fun x : {n : Denominator // n ∈ S} => (x.1 : ℕ) := by
    intro a b hab
    exact Subtype.ext (PNat.coe_injective hab)
  rw [Support.blockNat, Finset.card_image_of_injective _ hinj, Support.blockSize,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro x _
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

theorem Support.exists_denominator_of_mem_blockNat {c : S.Blocks} {m : ℕ}
    (hm : m ∈ S.blockNat c) :
    ∃ (x : Denominator) (h : x ∈ S),
      S.graph.connectedComponentMk ⟨x, h⟩ = c ∧ (x : ℕ) = m := by
  classical
  simp only [Support.blockNat, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at hm
  obtain ⟨x, hx, hval⟩ := hm
  exact ⟨x.1, x.2, hx, hval⟩

theorem Support.blockNat_nonempty (c : S.Blocks) : (S.blockNat c).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := c.exists_rep
  exact ⟨(x.1 : ℕ), (S.mem_blockNat_iff c x.1).2 ⟨x.2, hx⟩⟩

/-- The least denominator of a component. -/
noncomputable def Support.blockMin (c : S.Blocks) : ℕ :=
  (S.blockNat c).min' (S.blockNat_nonempty c)

/-- The greatest denominator of a component. -/
noncomputable def Support.blockMax (c : S.Blocks) : ℕ :=
  (S.blockNat c).max' (S.blockNat_nonempty c)

theorem Support.blockMin_mem (c : S.Blocks) : S.blockMin c ∈ S.blockNat c :=
  Finset.min'_mem _ _

theorem Support.blockMax_mem (c : S.Blocks) : S.blockMax c ∈ S.blockNat c :=
  Finset.max'_mem _ _

theorem Support.blockMin_le_blockMax (c : S.Blocks) : S.blockMin c ≤ S.blockMax c :=
  Finset.min'_le _ _ (S.blockMax_mem c)

/-- A connected component is exactly the integer interval it spans. -/
theorem Support.blockNat_eq_Icc (c : S.Blocks) :
    S.blockNat c = Finset.Icc (S.blockMin c) (S.blockMax c) := by
  classical
  apply Finset.Subset.antisymm
  · intro m hm
    exact Finset.mem_Icc.2 ⟨Finset.min'_le _ _ hm, Finset.le_max' _ _ hm⟩
  · intro m hm
    obtain ⟨hlow, hupp⟩ := Finset.mem_Icc.1 hm
    have hmpos : 0 < m :=
      lt_of_lt_of_le (S.pos_of_mem_blockNat (S.blockMin_mem c)) hlow
    obtain ⟨x, hxS, hxc, hxval⟩ :=
      S.exists_denominator_of_mem_blockNat (S.blockMin_mem c)
    obtain ⟨y, hyS, hyc, hyval⟩ :=
      S.exists_denominator_of_mem_blockNat (S.blockMax_mem c)
    have hsame : S.graph.connectedComponentMk ⟨x, hxS⟩ =
        S.graph.connectedComponentMk ⟨y, hyS⟩ := hxc.trans hyc.symm
    have h1 : min (x : ℕ) (y : ℕ) ≤ m := by
      rw [hxval, hyval]
      have := S.blockMin_le_blockMax c
      omega
    have h2 : m ≤ max (x : ℕ) (y : ℕ) := by
      rw [hxval, hyval]
      have := S.blockMin_le_blockMax c
      omega
    obtain ⟨hz, hzc⟩ :=
      Support.mem_of_between hxS hyS hsame (z := ⟨m, hmpos⟩) h1 h2
    exact (S.mem_blockNat_iff c ⟨m, hmpos⟩).2 ⟨hz, hzc.trans hxc⟩

theorem Support.blockMin_lt_blockMax {c : S.Blocks} (h : 2 ≤ S.blockSize c) :
    S.blockMin c < S.blockMax c := by
  have hcard := S.blockNat_card c
  rw [S.blockNat_eq_Icc c, Nat.card_Icc] at hcard
  have hle := S.blockMin_le_blockMax c
  omega

/-- Distinct components occupy disjoint sets of denominators. -/
theorem Support.blockNat_disjoint {c d : S.Blocks} (h : c ≠ d) :
    Disjoint (S.blockNat c) (S.blockNat d) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmc hmd
  have hmpos : 0 < m := S.pos_of_mem_blockNat hmc
  obtain ⟨hn, hc⟩ := (S.mem_blockNat_iff c ⟨m, hmpos⟩).1 (by simpa using hmc)
  obtain ⟨hn', hd⟩ := (S.mem_blockNat_iff d ⟨m, hmpos⟩).1 (by simpa using hmd)
  exact h (hc.symm.trans hd)

/--
Distinct components are not adjacent: no denominator of one is the successor of
a denominator of the other.  This is forced by the component structure, not by
the separation field of a physical constraint.
-/
theorem Support.blockNat_not_adjacent {c d : S.Blocks} (h : c ≠ d)
    {m : ℕ} (hm : m ∈ S.blockNat c) (hm' : m + 1 ∈ S.blockNat d) : False := by
  classical
  have hmpos : 0 < m := S.pos_of_mem_blockNat hm
  have hm'pos : 0 < m + 1 := Nat.succ_pos m
  obtain ⟨hn, hc⟩ := (S.mem_blockNat_iff c ⟨m, hmpos⟩).1 (by simpa using hm)
  obtain ⟨hn', hd⟩ := (S.mem_blockNat_iff d ⟨m + 1, hm'pos⟩).1 (by simpa using hm')
  have hadj : S.graph.Adj ⟨⟨m, hmpos⟩, hn⟩ ⟨⟨m + 1, hm'pos⟩, hn'⟩ := by
    change denominatorPath.Adj (⟨m, hmpos⟩ : Denominator) ⟨m + 1, hm'pos⟩
    exact Or.inl rfl
  exact h (((SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans hc).symm.trans hd)

/--
Reciprocal value is the sum of the component interval sums.  The component
index is presented through an explicit enumeration so that the statement needs
no decidability instance on the component quotient.
-/
theorem Support.value_eq_sum_blockNat (S : Support) {k : ℕ} (e : Fin k ≃ S.Blocks) :
    ∑ i : Fin k, ∑ m ∈ S.blockNat (e i), (m : ℚ)⁻¹ = S.value := by
  classical
  have hfibre : ∀ c : S.Blocks,
      ∑ m ∈ S.blockNat c, (m : ℚ)⁻¹ =
        ∑ x ∈ Finset.univ.filter
          fun x : {n : Denominator // n ∈ S} => S.graph.connectedComponentMk x = c,
          ((x.1 : ℕ) : ℚ)⁻¹ := by
    intro c
    rw [Support.blockNat, Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext (PNat.coe_injective hab)
  calc
    ∑ i : Fin k, ∑ m ∈ S.blockNat (e i), (m : ℚ)⁻¹
        = ∑ c : S.Blocks, ∑ m ∈ S.blockNat c, (m : ℚ)⁻¹ :=
        Equiv.sum_comp e fun c => ∑ m ∈ S.blockNat c, (m : ℚ)⁻¹
    _ = ∑ c : S.Blocks, ∑ x ∈ Finset.univ.filter
            fun x : {n : Denominator // n ∈ S} => S.graph.connectedComponentMk x = c,
            ((x.1 : ℕ) : ℚ)⁻¹ := Finset.sum_congr rfl fun c _ => hfibre c
    _ = ∑ x : {n : Denominator // n ∈ S}, ((x.1 : ℕ) : ℚ)⁻¹ :=
        Finset.sum_fiberwise Finset.univ (fun x => S.graph.connectedComponentMk x) _
    _ = ∑ n ∈ S, ((n : ℕ) : ℚ)⁻¹ := by
        rw [← Finset.attach_eq_univ, Finset.sum_attach S fun n => ((n : ℕ) : ℚ)⁻¹]
    _ = S.value := by
        rw [Support.value]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [reciprocal, one_div]
        rfl

end Blocks

/-! ## The literal statements -/

/--
Erdős problem 289 in the form used by the `erdos_289` entry of
`google-deepmind/formal-conjectures`: for all sufficiently large `k` there are
`k` pairwise disjoint integer intervals of length at least two whose reciprocal
sum is one.
-/
def Erdos289Literal : Prop :=
  ∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n : ℚ)⁻¹ = 1

/--
Erdős problem 289 as displayed on erdosproblems.com/289, where the intervals
are additionally required to be non-adjacent.  This is the stronger sentence:
adjacent intervals would merge into a single block.
-/
def Erdos289LiteralSeparated : Prop :=
  ∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n : ℚ)⁻¹ = 1

theorem erdos289Literal_of_separated (h : Erdos289LiteralSeparated) : Erdos289Literal := by
  filter_upwards [h] with k hk
  obtain ⟨I, hlen, hsep, hsum⟩ := hk
  exact ⟨I, hlen, fun i j hij => (hsep i j hij).imp (fun h => by omega) fun h => by omega, hsum⟩

/-- One saturation witness of grade `k` is literally a family of `k` blocks. -/
theorem exists_intervalFamily_of_saturationWitness
    {k : ℕ} (hk : 0 < k) (w : SaturationWitness 1 originalConstraint k) :
    ∃ I : Fin k → ℕ × ℕ,
      (∀ i, (I i).1 < (I i).2) ∧
      (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
      ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n : ℚ)⁻¹ = 1 := by
  classical
  set S := w.support with hS
  have hcard : Nat.card S.Blocks = k := w.grade_eq
  have hpos : Nat.card S.Blocks ≠ 0 := by rw [hcard]; omega
  let e : Fin k ≃ S.Blocks :=
    ((Nat.equivFinOfCardPos hpos).trans (finCongr hcard)).symm
  refine ⟨fun i => (S.blockMin (e i), S.blockMax (e i)), ?_, ?_, ?_⟩
  · intro i
    refine S.blockMin_lt_blockMax ?_
    have hsize : S.blockSize (e i) = 2 ∨ S.blockSize (e i) = 3 := w.admissible.1 (e i)
    omega
  · intro i j hij
    have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hdisj := S.blockNat_disjoint hne
    have hIi := S.blockNat_eq_Icc (e i)
    have hIj := S.blockNat_eq_Icc (e j)
    have hlei := S.blockMin_le_blockMax (e i)
    have hlej := S.blockMin_le_blockMax (e j)
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    -- `h1 : min (e j) ≤ max (e i) + 1` and `h2 : min (e i) ≤ max (e j) + 1`.
    -- Equality on either side would make the two components adjacent, and any
    -- strict inequality on both sides would make them overlap.
    rcases Nat.lt_or_ge (S.blockMax (e i)) (S.blockMin (e j)) with hgap | hoverlap
    · -- adjacency: `blockMin (e j) = blockMax (e i) + 1`
      have hEq : S.blockMin (e j) = S.blockMax (e i) + 1 := by omega
      refine S.blockNat_not_adjacent hne (S.blockMax_mem (e i)) ?_
      rw [← hEq]
      exact S.blockMin_mem (e j)
    · rcases Nat.lt_or_ge (S.blockMax (e j)) (S.blockMin (e i)) with hgap' | hoverlap'
      · have hEq : S.blockMin (e i) = S.blockMax (e j) + 1 := by omega
        refine S.blockNat_not_adjacent hne.symm (S.blockMax_mem (e j)) ?_
        rw [← hEq]
        exact S.blockMin_mem (e i)
      · -- genuine overlap
        set m := max (S.blockMin (e i)) (S.blockMin (e j)) with hm
        have hmi : m ∈ S.blockNat (e i) := by
          rw [hIi]; exact Finset.mem_Icc.2 ⟨le_max_left _ _, by omega⟩
        have hmj : m ∈ S.blockNat (e j) := by
          rw [hIj]; exact Finset.mem_Icc.2 ⟨le_max_right _ _, by omega⟩
        exact (Finset.disjoint_left.1 hdisj hmi) hmj
  · calc
      ∑ i : Fin k, ∑ n ∈ Finset.Icc (S.blockMin (e i)) (S.blockMax (e i)), (n : ℚ)⁻¹
          = ∑ i : Fin k, ∑ n ∈ S.blockNat (e i), (n : ℚ)⁻¹ :=
        Finset.sum_congr rfl fun i _ => by rw [S.blockNat_eq_Icc (e i)]
      _ = S.value := S.value_eq_sum_blockNat e
      _ = 1 := w.value_eq

/--
The intrinsic theorem implies the sentence displayed on erdosproblems.com/289.
-/
theorem erdos289LiteralSeparated_of_statement (h : Erdos289Statement) :
    Erdos289LiteralSeparated := by
  obtain ⟨N, hN⟩ := h
  refine Filter.eventually_atTop.2 ⟨max N 1, fun k hk => ?_⟩
  obtain ⟨w⟩ := hN k (le_trans (le_max_left N 1) hk)
  exact exists_intervalFamily_of_saturationWitness
    (lt_of_lt_of_le Nat.one_pos (le_trans (le_max_right N 1) hk)) w

/-- The intrinsic theorem implies the `formal-conjectures` form. -/
theorem erdos289Literal_of_statement (h : Erdos289Statement) : Erdos289Literal :=
  erdos289Literal_of_separated (erdos289LiteralSeparated_of_statement h)

end Erdos289
