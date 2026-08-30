import Packing.RowedGraph

/-!
# Leaf P — no-independent-transversal amalgamation and the sharp family

The disjoint sum of two finite rowed graphs along a dissolved row, the
amalgamation theorem P.6, and the sharp obstruction family P.7: for every
`d ≥ 1` a finite rowed graph of maximum degree `d` with exactly `2d` rows, each
of cardinality `2d - 1`, and no independent transversal.
-/

namespace Erdos289

universe u

/-! ## The disjoint sum of two simple graphs -/

/-- The disjoint sum of two simple graphs. -/
def graphSum {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V ⊕ W) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inr a, Sum.inr b => H.Adj a b
    | _, _ => False
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact h.symm
    · exact h.elim
    · exact h.elim
    · exact h.symm⟩
  loopless := ⟨by
    rintro (a | a) h
    · exact G.irrefl h
    · exact H.irrefl h⟩

@[simp]
theorem graphSum_inl_inl {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (a b : V) : (graphSum G H).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := Iff.rfl

@[simp]
theorem graphSum_inr_inr {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (a b : W) : (graphSum G H).Adj (Sum.inr a) (Sum.inr b) ↔ H.Adj a b := Iff.rfl

@[simp]
theorem graphSum_inl_inr {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (a : V) (b : W) : ¬ (graphSum G H).Adj (Sum.inl a) (Sum.inr b) := id

@[simp]
theorem graphSum_inr_inl {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    (a : W) (b : V) : ¬ (graphSum G H).Adj (Sum.inr a) (Sum.inl b) := id

instance graphSumDecRel {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (graphSum G H).Adj := by
  rintro (a | a) (b | b)
  · exact inferInstanceAs (Decidable (G.Adj a b))
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable (H.Adj a b))

/-- Independence in a summand is inherited from independence in the sum. -/
theorem isIndepSet_of_inl {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : Set (V ⊕ W)} (hs : (graphSum G H).IsIndepSet s) :
    G.IsIndepSet (Sum.inl ⁻¹' s) := by
  intro a ha b hb hab
  exact hs ha hb (by simpa using hab)

/-- Independence in a summand is inherited from independence in the sum. -/
theorem isIndepSet_of_inr {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W}
    {s : Set (V ⊕ W)} (hs : (graphSum G H).IsIndepSet s) :
    H.IsIndepSet (Sum.inr ⁻¹' s) := by
  intro a ha b hb hab
  exact hs ha hb (by simpa using hab)

namespace FiniteRowedGraph

/-! ## Amalgamation along a dissolved row -/

variable (G H : FiniteRowedGraph.{u}) (t : H.index) (alpha : H.vertex → G.index)

/-- The row map of the amalgam of `G` and `H` that dissolves the row `t` of `H`
into the rows of `G` along `alpha`. -/
def amalgamRow (v : G.vertex ⊕ H.vertex) : G.index ⊕ {j : H.index // j ≠ t} :=
  match v with
  | Sum.inl a => Sum.inl (G.row a)
  | Sum.inr b => if h : H.row b = t then Sum.inl (alpha b) else Sum.inr ⟨H.row b, h⟩

/-- P.6: the amalgam of two finite rowed graphs along a dissolved row. -/
def amalgam : FiniteRowedGraph.{u} where
  vertex := G.vertex ⊕ H.vertex
  graph := graphSum G.graph H.graph
  index := G.index ⊕ {j : H.index // j ≠ t}
  row := amalgamRow G H t alpha
  row_surjective := by
    rintro (i | ⟨j, hj⟩)
    · obtain ⟨a, ha⟩ := G.row_surjective i
      exact ⟨Sum.inl a, by simp [amalgamRow, ha]⟩
    · obtain ⟨b, hb⟩ := H.row_surjective j
      exact ⟨Sum.inr b, by simp [amalgamRow, hb, hj]⟩

@[simp]
theorem amalgam_row_inl (a : G.vertex) :
    (amalgam G H t alpha).row (Sum.inl a) = Sum.inl (G.row a) := rfl

theorem amalgam_row_inr (b : H.vertex) :
    (amalgam G H t alpha).row (Sum.inr b)
      = if h : H.row b = t then Sum.inl (alpha b) else Sum.inr ⟨H.row b, h⟩ := rfl

theorem amalgamRow_inl' (a : G.vertex) :
    amalgamRow G H t alpha (Sum.inl a) = Sum.inl (G.row a) := rfl

theorem amalgamRow_inr' (b : H.vertex) :
    amalgamRow G H t alpha (Sum.inr b)
      = if h : H.row b = t then Sum.inl (alpha b) else Sum.inr ⟨H.row b, h⟩ := rfl

/-- P.6: the amalgam of two rowed graphs without independent transversals again
has no independent transversal. -/
theorem noIT_amalgam (hG : IsEmpty (IndependentTransversal G))
    (hH : IsEmpty (IndependentTransversal H)) :
    IsEmpty (IndependentTransversal (amalgam G H t alpha)) := by
  classical
  refine ⟨fun T ↦ ?_⟩
  by_cases hall : ∀ i : G.index, ∃ a : G.vertex, T.pick (Sum.inl i) = Sum.inl a
  · -- every row of `G` is represented inside the `G`-summand
    refine hG.elim ?_
    refine (exists_independentTransversal_of_meets_rows
      (Finset.univ.filter fun a : G.vertex ↦ Sum.inl a ∈ T.carrier) ?_ ?_).some
    · refine (isIndepSet_of_inl (G := G.graph) (H := H.graph) T.indep).mono ?_
      intro a ha
      exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2
    · intro i
      obtain ⟨a, ha⟩ := hall i
      refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha ▸ T.pick_mem _⟩, ?_⟩
      have hrow := T.row_pick (Sum.inl i)
      rw [ha] at hrow
      exact Sum.inl.inj hrow
  · -- some row of `G` is represented by a vertex of the dissolved row of `H`
    simp only [not_forall, not_exists] at hall
    obtain ⟨i0, hi0⟩ := hall
    obtain ⟨b0, hb0⟩ : ∃ b : H.vertex, T.pick (Sum.inl i0) = Sum.inr b := by
      rcases hpick : T.pick (Sum.inl i0) with a | b
      · exact absurd hpick (hi0 a)
      · exact ⟨b, rfl⟩
    have hb0row : H.row b0 = t := by
      have hrow := T.row_pick (Sum.inl i0)
      rw [hb0, amalgam_row_inr] at hrow
      by_cases h : H.row b0 = t
      · exact h
      · rw [dif_neg h] at hrow; exact absurd hrow (by simp)
    refine hH.elim ?_
    refine (exists_independentTransversal_of_meets_rows
      (Finset.univ.filter fun b : H.vertex ↦ Sum.inr b ∈ T.carrier) ?_ ?_).some
    · refine (isIndepSet_of_inr (G := G.graph) (H := H.graph) T.indep).mono ?_
      intro b hb
      exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
    · intro j
      by_cases hj : j = t
      · subst hj
        exact ⟨b0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hb0 ▸ T.pick_mem _⟩, hb0row⟩
      · obtain ⟨b, hbj⟩ : ∃ b : H.vertex, T.pick (Sum.inr ⟨j, hj⟩) = Sum.inr b := by
          rcases hpick : T.pick (Sum.inr (⟨j, hj⟩ : {k : H.index // k ≠ t})) with a | b
          · have hrow := T.row_pick (Sum.inr (⟨j, hj⟩ : {k : H.index // k ≠ t}))
            rw [hpick, amalgam_row_inl] at hrow
            exact absurd hrow (by simp)
          · exact ⟨b, rfl⟩
        refine ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, hbj ▸ T.pick_mem _⟩, ?_⟩
        have hrow := T.row_pick (Sum.inr (⟨j, hj⟩ : {k : H.index // k ≠ t}))
        rw [hbj, amalgam_row_inr] at hrow
        by_cases h : H.row b = t
        · rw [dif_pos h] at hrow; exact absurd hrow (by simp)
        · rw [dif_neg h] at hrow
          exact congrArg Subtype.val (Sum.inr.inj hrow)

end FiniteRowedGraph

/-! ## Degrees in a disjoint sum -/

variable {V W : Type u} [Fintype V] [Fintype W]

theorem graphSum_neighborFinset_inl (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (a : V) :
    (graphSum G H).neighborFinset (Sum.inl a)
      = (G.neighborFinset a).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  ext v
  rcases v with b | b <;> simp [SimpleGraph.mem_neighborFinset]

theorem graphSum_neighborFinset_inr (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (a : W) :
    (graphSum G H).neighborFinset (Sum.inr a)
      = (H.neighborFinset a).map ⟨Sum.inr, Sum.inr_injective⟩ := by
  ext v
  rcases v with b | b <;> simp [SimpleGraph.mem_neighborFinset]

theorem graphSum_degree_inl (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (a : V) :
    (graphSum G H).degree (Sum.inl a) = G.degree a := by
  rw [SimpleGraph.degree, SimpleGraph.degree, graphSum_neighborFinset_inl, Finset.card_map]

theorem graphSum_degree_inr (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (a : W) :
    (graphSum G H).degree (Sum.inr a) = H.degree a := by
  rw [SimpleGraph.degree, SimpleGraph.degree, graphSum_neighborFinset_inr, Finset.card_map]

theorem maxDegree_graphSum_le (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] {d : ℕ}
    (hG : G.maxDegree ≤ d) (hH : H.maxDegree ≤ d) :
    (graphSum G H).maxDegree ≤ d := by
  refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ ?_
  rintro (a | a)
  · rw [graphSum_degree_inl]; exact le_trans (G.degree_le_maxDegree a) hG
  · rw [graphSum_degree_inr]; exact le_trans (H.degree_le_maxDegree a) hH

namespace FiniteRowedGraph

/-! ## Row cardinalities of an amalgam -/

variable (G H : FiniteRowedGraph.{u}) (t : H.index) (alpha : H.vertex → G.index)

theorem amalgam_rowCard_inr (j : {k : H.index // k ≠ t}) :
    (amalgam G H t alpha).rowCard (Sum.inr j) = H.rowCard j.1 := by
  classical
  show (Finset.univ.filter fun v : G.vertex ⊕ H.vertex ↦
      amalgamRow G H t alpha v = Sum.inr j).card = _
  have hset : (Finset.univ.filter fun v : G.vertex ⊕ H.vertex ↦
      amalgamRow G H t alpha v = Sum.inr j)
      = (H.rowFibre j.1).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, mem_rowFibre]
    rcases v with a | b
    · rw [amalgamRow_inl']
      constructor
      · intro hc; exact absurd hc (by simp)
      · rintro ⟨c, -, hc⟩; exact absurd hc (by simp)
    · rw [amalgamRow_inr']
      by_cases h : H.row b = t
      · rw [dif_pos h]
        constructor
        · intro hc; exact absurd hc (by simp)
        · rintro ⟨c, hc, hcb⟩
          cases Sum.inr_injective hcb
          exact absurd (hc.symm.trans h) j.2
      · rw [dif_neg h]
        constructor
        · intro hc; exact ⟨b, congrArg Subtype.val (Sum.inr.inj hc), rfl⟩
        · rintro ⟨c, hc, hcb⟩
          cases Sum.inr_injective hcb
          exact congrArg Sum.inr (Subtype.ext hc)
  rw [hset, Finset.card_map]
  rfl

theorem amalgam_rowCard_inl (i : G.index) :
    (amalgam G H t alpha).rowCard (Sum.inl i)
      = G.rowCard i + (((H.rowFibre t).filter fun b ↦ alpha b = i)).card := by
  classical
  show (Finset.univ.filter fun v : G.vertex ⊕ H.vertex ↦
      amalgamRow G H t alpha v = Sum.inl i).card = _
  have hdisj : Disjoint ((G.rowFibre i).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((((H.rowFibre t).filter fun b ↦ alpha b = i)).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    refine Finset.disjoint_left.2 ?_
    intro v hv hv'
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv hv'
    obtain ⟨a, -, rfl⟩ := hv
    obtain ⟨b, -, hb⟩ := hv'
    exact absurd hb (by simp)
  have hset : (Finset.univ.filter fun v : G.vertex ⊕ H.vertex ↦
      amalgamRow G H t alpha v = Sum.inl i)
      = (G.rowFibre i).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        (((H.rowFibre t).filter fun b ↦ alpha b = i)).map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk, mem_rowFibre]
    rcases v with a | b
    · rw [amalgamRow_inl']
      constructor
      · intro hc; exact Or.inl ⟨a, Sum.inl.inj hc, rfl⟩
      · rintro (⟨c, hc, hca⟩ | ⟨c, -, hca⟩)
        · cases Sum.inl_injective hca; exact congrArg Sum.inl hc
        · exact absurd hca (by simp)
    · rw [amalgamRow_inr']
      by_cases h : H.row b = t
      · rw [dif_pos h]
        constructor
        · intro hc
          exact Or.inr ⟨b, ⟨h, Sum.inl.inj hc⟩, rfl⟩
        · rintro (⟨c, -, hcb⟩ | ⟨c, hc, hcb⟩)
          · exact absurd hcb (by simp)
          · cases Sum.inr_injective hcb
            exact congrArg Sum.inl hc.2
      · rw [dif_neg h]
        constructor
        · intro hc; exact absurd hc (by simp)
        · rintro (⟨c, -, hcb⟩ | ⟨c, hc, hcb⟩)
          · exact absurd hcb (by simp)
          · cases Sum.inr_injective hcb
            exact absurd hc.1 h
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
  rfl

end FiniteRowedGraph

/-! ## The complete bipartite obstruction -/

/-- The complete bipartite graph `K_{d,d}` on `Fin 2 × Fin d`. -/
def bipartiteGraph (d : ℕ) : SimpleGraph (Fin 2 × Fin d) where
  Adj x y := x.1 ≠ y.1
  symm := ⟨by intro a b h; exact Ne.symm h⟩
  loopless := ⟨by intro a h; exact h rfl⟩

instance bipartiteGraphDecRel (d : ℕ) : DecidableRel (bipartiteGraph d).Adj :=
  fun x y ↦ inferInstanceAs (Decidable (x.1 ≠ y.1))

private theorem fin2_ne_iff : ∀ a b : Fin 2, a ≠ b ↔ b = a + 1 := by decide

theorem bipartiteGraph_degree (d : ℕ) (x : Fin 2 × Fin d) :
    (bipartiteGraph d).degree x = d := by
  classical
  have hfin : (bipartiteGraph d).neighborFinset x
      = ({x.1 + 1} : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin d)) := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, and_true]
    exact fin2_ne_iff x.1 y.1
  rw [SimpleGraph.degree, hfin, Finset.card_product, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin, one_mul]

theorem bipartiteGraph_maxDegree (d : ℕ) : (bipartiteGraph d).maxDegree ≤ d :=
  SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun v ↦ (bipartiteGraph_degree d v).le

/-- `K_{d,d}` as a finite rowed graph with two rows of cardinality `d`. -/
def completeBipartite (d : ℕ) (hd : 1 ≤ d) : FiniteRowedGraph.{0} where
  vertex := Fin 2 × Fin d
  graph := bipartiteGraph d
  index := Fin 2
  row := Prod.fst
  row_surjective := fun i ↦ ⟨(i, ⟨0, hd⟩), rfl⟩

theorem completeBipartite_rowCard (d : ℕ) (hd : 1 ≤ d) (i : Fin 2) :
    (completeBipartite d hd).rowCard i = d := by
  classical
  show (Finset.univ.filter fun v : Fin 2 × Fin d ↦ v.1 = i).card = d
  have hfib : (Finset.univ.filter fun v : Fin 2 × Fin d ↦ v.1 = i)
      = ({i} : Finset (Fin 2)) ×ˢ (Finset.univ : Finset (Fin d)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [hfib, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
    one_mul]

theorem completeBipartite_noIT (d : ℕ) (hd : 1 ≤ d) :
    IsEmpty (FiniteRowedGraph.IndependentTransversal (completeBipartite d hd)) := by
  refine ⟨fun T ↦ ?_⟩
  have h0 : (T.pick (0 : Fin 2)).1 = (0 : Fin 2) := T.row_pick (0 : Fin 2)
  have h1 : (T.pick (1 : Fin 2)).1 = (1 : Fin 2) := T.row_pick (1 : Fin 2)
  have hne : T.pick (0 : Fin 2) ≠ T.pick (1 : Fin 2) := by
    intro h
    rw [h, h1] at h0
    exact absurd h0 (by decide)
  have hadj : (completeBipartite d hd).graph.Adj (T.pick (0 : Fin 2)) (T.pick (1 : Fin 2)) := by
    show (T.pick (0 : Fin 2)).1 ≠ (T.pick (1 : Fin 2)).1
    rw [h0, h1]
    decide
  exact T.indep (Finset.mem_coe.2 (T.pick_mem _)) (Finset.mem_coe.2 (T.pick_mem _)) hne hadj

/-! ## The iterative sharp construction -/

private theorem exists_split {V : Type} [Fintype V] [DecidableEq V]
    (s : Finset V) (n : ℕ) (hn : n ≤ s.card) :
    ∃ f : V → Fin 2, (s.filter fun b ↦ f b = 0).card = n ∧
      (s.filter fun b ↦ f b = 1).card = s.card - n := by
  classical
  obtain ⟨u, hu, hcard⟩ := Finset.exists_subset_card_eq hn
  refine ⟨fun b ↦ if b ∈ u then 0 else 1, ?_, ?_⟩
  · have he : (s.filter fun b ↦ (if b ∈ u then (0 : Fin 2) else 1) = 0) = u := by
      ext b
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨-, hb⟩
        by_contra hbu
        rw [if_neg hbu] at hb
        exact absurd hb (by decide)
      · intro hb
        exact ⟨hu hb, by rw [if_pos hb]⟩
    rw [he, hcard]
  · have he : (s.filter fun b ↦ (if b ∈ u then (0 : Fin 2) else 1) = 1) = s \ u := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hbs, hb⟩
        refine ⟨hbs, fun hbu ↦ ?_⟩
        rw [if_pos hbu] at hb
        exact absurd hb (by decide)
      · rintro ⟨hbs, hbu⟩
        exact ⟨hbs, by rw [if_neg hbu]⟩
    rw [he, Finset.card_sdiff, Finset.inter_eq_left.2 hu, hcard]

/-- The invariant of the iterative construction of the sharp obstruction family:
a rowed graph of maximum degree `d` with `r` rows, a distinguished row of
cardinality `m`, an untouched row of cardinality `sm`, all other rows of
cardinality `2d-1`, and no independent transversal. -/
private structure SharpStage (d m sm r : ℕ) where
  toRowed : FiniteRowedGraph.{0}
  degree_le : toRowed.graph.maxDegree ≤ d
  exists_degree : ∃ v, toRowed.graph.degree v = d
  noIT : IsEmpty (FiniteRowedGraph.IndependentTransversal toRowed)
  big : toRowed.index
  small : toRowed.index
  big_ne_small : big ≠ small
  card_big : toRowed.rowCard big = m
  card_small : toRowed.rowCard small = sm
  card_other : ∀ i, i ≠ big → i ≠ small → toRowed.rowCard i = 2 * d - 1
  card_index : Fintype.card toRowed.index = r

private def SharpStage.swap {d m sm r : ℕ} (S : SharpStage d m sm r) : SharpStage d sm m r :=
  { S with
    big := S.small
    small := S.big
    big_ne_small := S.big_ne_small.symm
    card_big := S.card_small
    card_small := S.card_big
    card_other := fun i h1 h2 ↦ S.card_other i h2 h1 }

private theorem sharpStage_base (d : ℕ) (hd : 1 ≤ d) : Nonempty (SharpStage d d d 2) := by
  have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  exact ⟨{ toRowed := completeBipartite d hd
           degree_le := bipartiteGraph_maxDegree d
           exists_degree := ⟨((0 : Fin 2), ⟨0, hd⟩), bipartiteGraph_degree d _⟩
           noIT := completeBipartite_noIT d hd
           big := (0 : Fin 2)
           small := (1 : Fin 2)
           big_ne_small := (show (0 : Fin 2) ≠ (1 : Fin 2) by decide)
           card_big := completeBipartite_rowCard d hd 0
           card_small := completeBipartite_rowCard d hd 1
           card_other := by
             intro i h0 h1
             rcases hfin2 i with rfl | rfl
             · exact absurd rfl h0
             · exact absurd rfl h1
           card_index := Fintype.card_fin 2 }⟩

private theorem sharpStage_step {d m sm r : ℕ} (hd : 1 ≤ d) (S : SharpStage d m sm r)
    (n₀ n₁ : ℕ) (hsplit : m = n₀ + n₁) (hn₁ : n₁ = d - 1) :
    Nonempty (SharpStage d (d + n₀) sm (r + 1)) := by
  classical
  have hbigcard : (S.toRowed.rowFibre S.big).card = m := S.card_big
  obtain ⟨f, hf0, hf1⟩ := exists_split (S.toRowed.rowFibre S.big) n₀ (by omega)
  have hrpos : 0 < r := by
    rw [← S.card_index]
    exact Fintype.card_pos_iff.2 ⟨S.big⟩
  have hsubcard : Fintype.card {j : S.toRowed.index // j ≠ S.big} = r - 1 := by
    have h1 : Fintype.card {j : S.toRowed.index // ¬ (j = S.big)}
        = Fintype.card S.toRowed.index - Fintype.card {j : S.toRowed.index // j = S.big} :=
      Fintype.card_subtype_compl _
    rw [h1, Fintype.card_subtype_eq, S.card_index]
  obtain ⟨v0, hv0⟩ := S.exists_degree
  refine ⟨{ toRowed := FiniteRowedGraph.amalgam (completeBipartite d hd) S.toRowed S.big f
            degree_le := maxDegree_graphSum_le (bipartiteGraph d) S.toRowed.graph
              (bipartiteGraph_maxDegree d) S.degree_le
            exists_degree := ⟨Sum.inr v0, by
              show (graphSum (bipartiteGraph d) S.toRowed.graph).degree (Sum.inr v0) = d
              rw [graphSum_degree_inr]
              exact hv0⟩
            noIT := FiniteRowedGraph.noIT_amalgam _ _ _ _ (completeBipartite_noIT d hd) S.noIT
            big := Sum.inl (0 : Fin 2)
            small := Sum.inr ⟨S.small, S.big_ne_small.symm⟩
            big_ne_small := by
              show (Sum.inl (0 : Fin 2) : Fin 2 ⊕ {j : S.toRowed.index // j ≠ S.big})
                  ≠ Sum.inr ⟨S.small, S.big_ne_small.symm⟩
              simp
            card_big := ?_
            card_small := ?_
            card_other := ?_
            card_index := ?_ }⟩
  · have h := FiniteRowedGraph.amalgam_rowCard_inl (completeBipartite d hd) S.toRowed S.big f
      (0 : Fin 2)
    rw [h, completeBipartite_rowCard]
    exact congrArg (fun x ↦ d + x) hf0
  · have h := FiniteRowedGraph.amalgam_rowCard_inr (completeBipartite d hd) S.toRowed S.big f
      ⟨S.small, S.big_ne_small.symm⟩
    rw [h]
    exact S.card_small
  · have hfin : ∀ y : Fin 2, y = 0 ∨ y = 1 := by decide
    rintro (x | ⟨j, hj⟩) h1 h2
    · rcases hfin x with rfl | rfl
      · exact absurd rfl h1
      · have h := FiniteRowedGraph.amalgam_rowCard_inl (completeBipartite d hd) S.toRowed S.big f
          (1 : Fin 2)
        rw [h, completeBipartite_rowCard]
        have h2 : (Finset.filter (fun b ↦ f b = (1 : Fin 2))
            (S.toRowed.rowFibre S.big)).card = n₁ := by
          rw [hf1, hbigcard]; omega
        refine (congrArg (fun x ↦ d + x) h2).trans ?_
        omega
    · have h := FiniteRowedGraph.amalgam_rowCard_inr (completeBipartite d hd) S.toRowed S.big f
        ⟨j, hj⟩
      rw [h]
      refine S.card_other j hj fun hjs ↦ h2 ?_
      exact congrArg Sum.inr (Subtype.ext hjs)
  · show Fintype.card (Fin 2 ⊕ {j : S.toRowed.index // j ≠ S.big}) = r + 1
    rw [Fintype.card_sum, Fintype.card_fin, hsubcard]
    omega

private theorem sharpStage_iterate (d sm r : ℕ) (hd : 1 ≤ d)
    (h : Nonempty (SharpStage d d sm r)) :
    ∀ k, Nonempty (SharpStage d (d + k) sm (r + k)) := by
  intro k
  induction k with
  | zero => simpa using h
  | succ k ih =>
      obtain ⟨S⟩ := ih
      exact sharpStage_step hd S (k + 1) (d - 1) (by omega) rfl

/-- P.7: for every `d ≥ 1` there is a finite rowed graph of maximum degree `d`
with exactly `2d` rows, every row of cardinality `2d - 1`, and no independent
transversal. -/
theorem sharpNoIndependentTransversal (d : ℕ) (hd : 1 ≤ d) :
    ∃ G : FiniteRowedGraph.{0},
      G.graph.maxDegree = d ∧
      Fintype.card G.index = 2 * d ∧
      (∀ i, G.rowCard i = 2 * d - 1) ∧
      IsEmpty (FiniteRowedGraph.IndependentTransversal G) := by
  have e1 : d + (d - 1) = 2 * d - 1 := by omega
  have e2 : 2 + (d - 1) = d + 1 := by omega
  have H1 : Nonempty (SharpStage d (2 * d - 1) d (d + 1)) := by
    have h := sharpStage_iterate d d 2 hd (sharpStage_base d hd) (d - 1)
    rwa [e1, e2] at h
  obtain ⟨S1⟩ := H1
  have e4 : d + 1 + (d - 1) = 2 * d := by omega
  have H3 : Nonempty (SharpStage d (2 * d - 1) (2 * d - 1) (2 * d)) := by
    have h := sharpStage_iterate d (2 * d - 1) (d + 1) hd ⟨S1.swap⟩ (d - 1)
    rwa [e1, e4] at h
  obtain ⟨S⟩ := H3
  refine ⟨S.toRowed, ?_, S.card_index, ?_, S.noIT⟩
  · obtain ⟨v, hv⟩ := S.exists_degree
    refine le_antisymm S.degree_le ?_
    calc d = S.toRowed.graph.degree v := hv.symm
      _ ≤ S.toRowed.graph.maxDegree := S.toRowed.graph.degree_le_maxDegree v
  · intro i
    by_cases h1 : i = S.big
    · rw [h1, S.card_big]
    · by_cases h2 : i = S.small
      · rw [h2, S.card_small]
      · exact S.card_other i h1 h2

end Erdos289
