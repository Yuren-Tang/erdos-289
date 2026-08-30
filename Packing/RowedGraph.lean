import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Finite rowed graphs

The carrier of leaf P: a finite simple graph together with a finite row index
object and a surjective row map.  Rows are the fibres of that map, so they form
a finite partition of the vertex object.  An independent transversal is an
independent vertex subobject meeting every row in exactly one vertex.
-/

namespace Erdos289

universe u

/-- A finite rowed graph `(G, I, ρ)`: a finite simple graph on a finite vertex
object, a finite row index object, and a surjective row map. -/
structure FiniteRowedGraph where
  /-- The finite vertex object. -/
  vertex : Type u
  /-- Finiteness of the vertex object. -/
  [vertexFintype : Fintype vertex]
  /-- Decidable equality of vertices. -/
  [vertexDecEq : DecidableEq vertex]
  /-- The simple graph carried by the vertex object. -/
  graph : SimpleGraph vertex
  /-- Decidability of adjacency. -/
  [adjDec : DecidableRel graph.Adj]
  /-- The finite row index object. -/
  index : Type u
  /-- Finiteness of the row index object. -/
  [indexFintype : Fintype index]
  /-- Decidable equality of row indices. -/
  [indexDecEq : DecidableEq index]
  /-- The row map. -/
  row : vertex → index
  /-- Every row index is used. -/
  row_surjective : Function.Surjective row

attribute [instance] FiniteRowedGraph.vertexFintype FiniteRowedGraph.vertexDecEq
  FiniteRowedGraph.adjDec FiniteRowedGraph.indexFintype FiniteRowedGraph.indexDecEq

namespace FiniteRowedGraph

variable (G : FiniteRowedGraph.{u})

/-- The row indexed by `i`: the fibre of the row map. -/
def rowFibre (i : G.index) : Finset G.vertex :=
  Finset.univ.filter fun v ↦ G.row v = i

/-- The cardinality of a row. -/
def rowCard (i : G.index) : ℕ := (G.rowFibre i).card

variable {G}

@[simp]
theorem mem_rowFibre {v : G.vertex} {i : G.index} :
    v ∈ G.rowFibre i ↔ G.row v = i := by
  simp [rowFibre]

theorem mem_rowFibre_row (v : G.vertex) : v ∈ G.rowFibre (G.row v) :=
  mem_rowFibre.2 rfl

/-- Distinct rows are disjoint. -/
theorem rowFibre_disjoint {i j : G.index} (h : i ≠ j) :
    Disjoint (G.rowFibre i) (G.rowFibre j) := by
  refine Finset.disjoint_left.2 fun v hv hv' ↦ ?_
  rw [mem_rowFibre] at hv hv'
  exact h (hv ▸ hv')

/-- The rows cover the vertex object. -/
theorem rowFibre_cover : (Finset.univ : Finset G.index).biUnion G.rowFibre = Finset.univ := by
  refine Finset.eq_univ_of_forall fun v ↦ ?_
  exact Finset.mem_biUnion.2 ⟨G.row v, Finset.mem_univ _, mem_rowFibre_row v⟩

/-- Every row is nonempty, since the row map is surjective. -/
theorem rowFibre_nonempty (i : G.index) : (G.rowFibre i).Nonempty := by
  obtain ⟨v, hv⟩ := G.row_surjective i
  exact ⟨v, mem_rowFibre.2 hv⟩

theorem rowCard_pos (i : G.index) : 0 < G.rowCard i :=
  Finset.card_pos.2 (rowFibre_nonempty i)

/-- The rows partition the vertex object: their cardinalities sum to the
cardinality of the vertex object. -/
theorem sum_rowCard : ∑ i : G.index, G.rowCard i = Fintype.card G.vertex := by
  classical
  simp only [rowCard]
  rw [← Finset.card_biUnion fun i _ j _ h ↦ rowFibre_disjoint h, rowFibre_cover]
  rfl

variable (G)

/-- The finite independent vertex subobjects of a rowed graph. -/
structure IndepSubobject where
  /-- The underlying finite vertex subobject. -/
  carrier : Finset G.vertex
  /-- Independence of the subobject. -/
  indep : G.graph.IsIndepSet (carrier : Set G.vertex)

/-- An independent transversal: an independent vertex subobject meeting every
row in exactly one vertex. -/
structure IndependentTransversal extends IndepSubobject G where
  /-- Every row is met in exactly one vertex. -/
  meets_row : ∀ i : G.index, (toIndepSubobject.carrier ∩ G.rowFibre i).card = 1

variable {G}

namespace IndepSubobject

/-- Every subobject of an independent subobject is independent. -/
theorem subset (S : IndepSubobject G) {T : Finset G.vertex} (h : T ⊆ S.carrier) :
    G.graph.IsIndepSet (T : Set G.vertex) :=
  S.indep.mono (by exact_mod_cast h)

end IndepSubobject

namespace IndependentTransversal

/-- The vertex an independent transversal selects in a given row. -/
noncomputable def pick (S : IndependentTransversal G) (i : G.index) : G.vertex :=
  (Finset.card_eq_one.1 (S.meets_row i)).choose

theorem pick_spec (S : IndependentTransversal G) (i : G.index) :
    S.carrier ∩ G.rowFibre i = {S.pick i} :=
  (Finset.card_eq_one.1 (S.meets_row i)).choose_spec

theorem pick_mem (S : IndependentTransversal G) (i : G.index) : S.pick i ∈ S.carrier := by
  have h : S.pick i ∈ S.carrier ∩ G.rowFibre i := by
    rw [S.pick_spec i]
    exact Finset.mem_singleton_self _
  exact (Finset.mem_inter.1 h).1

theorem row_pick (S : IndependentTransversal G) (i : G.index) : G.row (S.pick i) = i := by
  have h : S.pick i ∈ S.carrier ∩ G.rowFibre i := by
    rw [S.pick_spec i]
    exact Finset.mem_singleton_self _
  exact mem_rowFibre.1 (Finset.mem_inter.1 h).2

/-- An independent transversal meets every row. -/
theorem exists_mem_row (S : IndependentTransversal G) (i : G.index) :
    ∃ v ∈ S.carrier, G.row v = i :=
  ⟨S.pick i, S.pick_mem i, S.row_pick i⟩

end IndependentTransversal

/-- A vertex subobject that meets every row and is independent yields an
independent transversal, after selecting one vertex per row. -/
theorem exists_independentTransversal_of_meets_rows
    (S : Finset G.vertex) (hS : G.graph.IsIndepSet (S : Set G.vertex))
    (hmeet : ∀ i : G.index, ∃ v ∈ S, G.row v = i) :
    Nonempty (IndependentTransversal G) := by
  classical
  choose f hfS hfrow using hmeet
  refine ⟨{ carrier := Finset.univ.image f
            indep := ?_
            meets_row := ?_ }⟩
  · refine hS.mono ?_
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ] at hv
    obtain ⟨i, -, rfl⟩ := hv
    exact hfS i
  · intro i
    have himage : (Finset.univ.image f) ∩ G.rowFibre i = {f i} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      refine ⟨Finset.mem_inter.2 ⟨Finset.mem_image_of_mem f (Finset.mem_univ i),
        mem_rowFibre.2 (hfrow i)⟩, ?_⟩
      intro x hx
      obtain ⟨hximg, hxrow⟩ := Finset.mem_inter.1 hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hximg
      rw [mem_rowFibre, hfrow j] at hxrow
      exact congrArg f hxrow
    rw [himage, Finset.card_singleton]

/-- Restricting a graph to an induced subgraph does not increase the maximum
degree. -/
theorem maxDegree_induce_le {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (s : Set V) [Fintype s]
    [DecidableRel (H.induce s).Adj] :
    (H.induce s).maxDegree ≤ H.maxDegree := by
  classical
  refine SimpleGraph.maxDegree_le_of_forall_degree_le _ _ fun v ↦ ?_
  refine le_trans ?_ (H.degree_le_maxDegree (v : V))
  rw [SimpleGraph.degree, SimpleGraph.degree]
  refine Finset.card_le_card_of_injOn (fun w ↦ (w : V)) (fun w hw ↦ ?_)
    (fun a _ b _ hab ↦ Subtype.ext hab)
  simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
  exact hw

end FiniteRowedGraph

end Erdos289
