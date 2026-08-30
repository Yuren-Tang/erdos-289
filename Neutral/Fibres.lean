import Reciprocal.State

/-!
# Leaf N — neutral fibres

Neutral pairs are pairs of E289 states with equal reciprocal value; the neutral
fibres are the loci of prescribed component-profile difference.  This file also
carries the block machinery used by the two fixed neutral certificates: a finite
family of pairwise separated consecutive runs in the successor graph determines
a state whose connected components are exactly those runs.
-/

open scoped BigOperators

namespace Erdos289

set_option linter.style.haveILetI false

/-! ## Separated runs in the successor graph -/

/-- The consecutive run of `k` vertices starting at `v`. -/
def successorRun (v : ℕ+) (k : ℕ) : Set ℕ+ :=
  {w : ℕ+ | (v : ℕ) ≤ (w : ℕ) ∧ (w : ℕ) < (v : ℕ) + k}

theorem mem_successorRun {v w : ℕ+} {k : ℕ} :
    w ∈ successorRun v k ↔ (v : ℕ) ≤ (w : ℕ) ∧ (w : ℕ) < (v : ℕ) + k :=
  Iff.rfl

/-- The `j`-th vertex of the run starting at `v`. -/
def runVertex (v : ℕ+) (j : ℕ) : ℕ+ := ⟨(v : ℕ) + j, by have := v.pos; omega⟩

theorem runVertex_coe (v : ℕ+) (j : ℕ) : ((runVertex v j : ℕ+) : ℕ) = (v : ℕ) + j := rfl

theorem runVertex_mem (v : ℕ+) {k j : ℕ} (hj : j < k) : runVertex v j ∈ successorRun v k := by
  rw [mem_successorRun, runVertex_coe]
  omega

theorem successorRun_eq_range (v : ℕ+) (k : ℕ) :
    successorRun v k = Set.range fun j : Fin k ↦ runVertex v (j : ℕ) := by
  ext w
  rw [mem_successorRun, Set.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(w : ℕ) - (v : ℕ), by omega⟩, PNat.coe_injective ?_⟩
    show (v : ℕ) + ((w : ℕ) - (v : ℕ)) = (w : ℕ)
    omega
  · rintro ⟨j, rfl⟩
    have hj := j.2
    rw [runVertex_coe]
    omega

theorem successorRun_finite (v : ℕ+) (k : ℕ) : (successorRun v k).Finite := by
  rw [successorRun_eq_range]
  exact Set.finite_range _

/-- A finite family of consecutive runs, pairwise separated by graph distance at
least two. -/
structure RunFamily (n : ℕ) where
  /-- The starting vertex of each run. -/
  start : Fin n → ℕ+
  /-- The length of each run. -/
  len : Fin n → ℕ
  /-- Every run is nonempty. -/
  len_pos : ∀ i, 0 < len i
  /-- Distinct runs are separated by graph distance at least two. -/
  separated : ∀ i j : Fin n, i ≠ j → ∀ u ∈ successorRun (start i) (len i),
    ∀ w ∈ successorRun (start j) (len j), 2 ≤ successorDist u w

namespace RunFamily

variable {n : ℕ} (R : RunFamily n)

/-- The `i`-th block of a run family. -/
def block (i : Fin n) : Set ℕ+ := successorRun (R.start i) (R.len i)

theorem mem_block {i : Fin n} {w : ℕ+} :
    w ∈ R.block i ↔ ((R.start i : ℕ+) : ℕ) ≤ (w : ℕ) ∧
      (w : ℕ) < ((R.start i : ℕ+) : ℕ) + R.len i :=
  Iff.rfl

/-- The vertex support of a run family. -/
def support : Set ℕ+ := ⋃ i, R.block i

theorem block_finite (i : Fin n) : (R.block i).Finite := successorRun_finite _ _

theorem support_finite : R.support.Finite :=
  Set.finite_iUnion fun i ↦ R.block_finite i

variable {R}

theorem mem_support {w : ℕ+} : w ∈ R.support ↔ ∃ i, w ∈ R.block i := Set.mem_iUnion

theorem block_disjoint {i j : Fin n} (hij : i ≠ j) {u : ℕ+} (hu : u ∈ R.block i)
    (hu' : u ∈ R.block j) : False := by
  have h := R.separated i j hij u hu u hu'
  rw [successorDist_self] at h
  omega

variable (R)

/-- The block index of a vertex of the support. -/
noncomputable def index (x : (R.support : Set ℕ+)) : Fin n :=
  (mem_support.1 x.2).choose

theorem mem_block_index (x : (R.support : Set ℕ+)) : (x : ℕ+) ∈ R.block (R.index x) :=
  (mem_support.1 x.2).choose_spec

variable {R}

theorem index_eq {i : Fin n} {x : (R.support : Set ℕ+)} (h : (x : ℕ+) ∈ R.block i) :
    R.index x = i := by
  by_contra hne
  exact block_disjoint hne (R.mem_block_index x) h

/-- Adjacent vertices of the support lie in the same block. -/
theorem index_eq_of_dist_le_one {x y : (R.support : Set ℕ+)}
    (h : successorDist (x : ℕ+) (y : ℕ+) ≤ 1) : R.index x = R.index y := by
  by_contra hne
  have h2 := R.separated (R.index x) (R.index y) hne _ (R.mem_block_index x) _
    (R.mem_block_index y)
  have h3 : (2 : ℕ) ≤ 1 := le_trans h2 h
  omega

/-- Vertices of one block are connected in the induced graph. -/
private theorem eqvGen_of_index_eq_aux (R : RunFamily n) (d : ℕ) :
    ∀ x y : (R.support : Set ℕ+), R.index x = R.index y →
      ((y : ℕ+) : ℕ) = ((x : ℕ+) : ℕ) + d →
      Relation.EqvGen (inducedGraph successorGraph R.support).Rel x y := by
  induction d with
  | zero =>
      intro x y _ hxy
      have hxy' : x = y := Subtype.ext (PNat.coe_injective (by omega))
      exact hxy' ▸ Relation.EqvGen.refl x
  | succ d ih =>
      intro x y hidx hxy
      have hxpos : 0 < ((x : ℕ+) : ℕ) + d := by have := ((x : ℕ+)).pos; omega
      obtain ⟨hx1, hx2⟩ := R.mem_block_index x
      have hyb0 := R.mem_block_index y
      rw [← hidx] at hyb0
      obtain ⟨hy1, hy2⟩ := hyb0
      set z : ℕ+ := ⟨((x : ℕ+) : ℕ) + d, hxpos⟩ with hzdef
      have hzcoe : ((z : ℕ+) : ℕ) = ((x : ℕ+) : ℕ) + d := rfl
      have hzblock : z ∈ R.block (R.index x) := by
        refine ⟨?_, ?_⟩ <;> rw [hzcoe] <;> omega
      have hzsupp : z ∈ R.support := mem_support.2 ⟨_, hzblock⟩
      have h1 : Relation.EqvGen (inducedGraph successorGraph R.support).Rel x ⟨z, hzsupp⟩ :=
        ih x ⟨z, hzsupp⟩ (index_eq hzblock).symm hzcoe
      have hdist : successorDist z (y : ℕ+) ≤ 1 := by
        simp only [successorDist, hzcoe]
        omega
      exact Relation.EqvGen.trans _ _ _ h1 (Relation.EqvGen.rel _ _ hdist)

theorem eqvGen_of_index_eq {n : ℕ} {R : RunFamily n} {x y : (R.support : Set ℕ+)}
    (h : R.index x = R.index y) :
    Relation.EqvGen (inducedGraph successorGraph R.support).Rel x y := by
  rcases Nat.le_total ((x : ℕ+) : ℕ) ((y : ℕ+) : ℕ) with hle | hle
  · exact eqvGen_of_index_eq_aux R (((y : ℕ+) : ℕ) - ((x : ℕ+) : ℕ)) x y h (by omega)
  · exact Relation.EqvGen.symm _ _
      (eqvGen_of_index_eq_aux R (((x : ℕ+) : ℕ) - ((y : ℕ+) : ℕ)) y x h.symm (by omega))

variable (R)

/-- The block index of a connected component. -/
noncomputable def componentIndex :
    PiZeroObj (inducedGraph successorGraph R.support) → Fin n :=
  Quotient.lift R.index fun x y hxy ↦ by
    induction hxy with
    | rel a b hab => exact index_eq_of_dist_le_one hab
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ h1 h2 => exact h1.trans h2

theorem componentIndex_mk (x : (R.support : Set ℕ+)) :
    R.componentIndex (piZeroMk _ x) = R.index x := rfl

theorem start_mem_block (i : Fin n) : R.start i ∈ R.block i := by
  refine ⟨le_rfl, ?_⟩
  have := R.len_pos i
  omega

theorem start_mem_support (i : Fin n) : R.start i ∈ R.support :=
  mem_support.2 ⟨i, R.start_mem_block i⟩

/-- The connected component carried by the `i`-th block. -/
noncomputable def componentOfBlock (i : Fin n) :
    PiZeroObj (inducedGraph successorGraph R.support) :=
  piZeroMk _ ⟨R.start i, R.start_mem_support i⟩

theorem componentIndex_componentOfBlock (i : Fin n) :
    R.componentIndex (R.componentOfBlock i) = i :=
  index_eq (R.start_mem_block i)

theorem componentOfBlock_componentIndex
    (c : PiZeroObj (inducedGraph successorGraph R.support)) :
    R.componentOfBlock (R.componentIndex c) = c := by
  induction c using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    exact eqvGen_of_index_eq (index_eq (R.start_mem_block (R.index x)))

/-- The connected components of a run family are exactly its blocks. -/
noncomputable def componentEquiv :
    PiZeroObj (inducedGraph successorGraph R.support) ≃ Fin n where
  toFun := R.componentIndex
  invFun := R.componentOfBlock
  left_inv := R.componentOfBlock_componentIndex
  right_inv := R.componentIndex_componentOfBlock

/-- The vertices of the component carried by the `i`-th block are exactly the
vertices of that block. -/
noncomputable def fibreEquiv (i : Fin n) :
    Fin (R.len i) ≃ ComponentFiber successorGraph R.support (R.componentOfBlock i) := by
  refine Equiv.ofBijective
    (fun j ↦ ⟨⟨runVertex (R.start i) (j : ℕ),
      mem_support.2 ⟨i, runVertex_mem _ j.2⟩⟩, ?_⟩) ⟨?_, ?_⟩
  · have h1 : R.index ⟨runVertex (R.start i) (j : ℕ),
        mem_support.2 ⟨i, runVertex_mem _ j.2⟩⟩ = i := index_eq (runVertex_mem _ j.2)
    have h2 : R.index ⟨R.start i, R.start_mem_support i⟩ = i :=
      index_eq (R.start_mem_block i)
    exact Quotient.sound (eqvGen_of_index_eq (h1.trans h2.symm))
  · intro a b hab
    have h : ((runVertex (R.start i) (a : ℕ) : ℕ+) : ℕ)
        = ((runVertex (R.start i) (b : ℕ) : ℕ+) : ℕ) :=
      congrArg (fun x : ℕ+ ↦ (x : ℕ)) (congrArg Subtype.val (congrArg Subtype.val hab))
    rw [runVertex_coe, runVertex_coe] at h
    exact Fin.ext (by omega)
  · rintro ⟨x, hx⟩
    have hidx : R.index x = i :=
      (congrArg R.componentIndex hx).trans (R.componentIndex_componentOfBlock i)
    have hxb := R.mem_block_index x
    rw [hidx] at hxb
    obtain ⟨xv, hxv⟩ : ∃ v : ℕ+, x.1 = v := ⟨x.1, rfl⟩
    rw [hxv] at hxb
    obtain ⟨hx1, hx2⟩ := hxb
    refine ⟨⟨(xv : ℕ) - ((R.start i : ℕ+) : ℕ), by omega⟩, ?_⟩
    have key : ((runVertex (R.start i) ((xv : ℕ) - ((R.start i : ℕ+) : ℕ)) : ℕ+) : ℕ)
        = (xv : ℕ) := by
      show ((R.start i : ℕ+) : ℕ) + ((xv : ℕ) - ((R.start i : ℕ+) : ℕ)) = (xv : ℕ)
      omega
    refine Subtype.ext (Subtype.ext ?_)
    show runVertex (R.start i) ((xv : ℕ) - ((R.start i : ℕ+) : ℕ)) = x.1
    rw [hxv]
    exact PNat.coe_injective key

/-- The component carried by the `i`-th block has exactly the length of that
block as its cardinality. -/
theorem componentCardinality_componentOfBlock (i : Fin n) :
    componentCardinality successorGraph R.support R.support_finite (R.componentOfBlock i)
      = ⟨R.len i, R.len_pos i⟩ := by
  letI : Finite (inducedGraph successorGraph R.support).carrier := R.support_finite
  letI : Finite (ComponentFiber successorGraph R.support (R.componentOfBlock i)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (ComponentFiber successorGraph R.support (R.componentOfBlock i)) :=
    Fintype.ofFinite _
  apply Subtype.ext
  change Fintype.card (ComponentFiber successorGraph R.support (R.componentOfBlock i))
    = R.len i
  rw [← Fintype.card_fin (R.len i)]
  exact (Fintype.card_congr (R.fibreEquiv i)).symm

/-- Every component of a run family is one of its blocks. -/
theorem componentCardinality_mem
    (hlen : ∀ j : Fin n, (⟨R.len j, R.len_pos j⟩ : ℕ+) ∈ allowedComponentTypes)
    (c : PiZeroObj (inducedGraph successorGraph R.support)) :
    componentCardinality successorGraph R.support R.support_finite c ∈
      allowedComponentTypes := by
  have hc := R.componentOfBlock_componentIndex c
  have hcard := R.componentCardinality_componentOfBlock (R.componentIndex c)
  rw [hc] at hcard
  rw [hcard]
  exact hlen _

end RunFamily

end Erdos289
