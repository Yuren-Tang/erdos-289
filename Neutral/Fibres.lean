import Reciprocal.State

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

/-- The vertices of a run family are indexed by the disjoint union of its runs. -/
noncomputable def supportEquiv :
    (Σ i : Fin n, Fin (R.len i)) ≃ (R.support : Set ℕ+) := by
  refine Equiv.ofBijective
    (fun p ↦ ⟨runVertex (R.start p.1) (p.2 : ℕ),
      mem_support.2 ⟨p.1, runVertex_mem _ p.2.2⟩⟩) ⟨?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have hv : (runVertex (R.start i) (j : ℕ) : ℕ+) = runVertex (R.start i') (j' : ℕ) :=
      congrArg Subtype.val h
    have hi : i = i' := by
      by_contra hne
      refine block_disjoint hne (runVertex_mem (R.start i) j.2) ?_
      rw [hv]
      exact runVertex_mem _ j'.2
    subst hi
    have hj : (j : ℕ) = (j' : ℕ) := by
      have := congrArg (fun x : ℕ+ ↦ (x : ℕ)) hv
      rw [runVertex_coe, runVertex_coe] at this
      omega
    simp [Fin.ext hj]
  · rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := mem_support.1 hx
    obtain ⟨xv, hxv⟩ : ∃ v : ℕ+, x = v := ⟨x, rfl⟩
    rw [hxv] at hi
    obtain ⟨hx1, hx2⟩ := hi
    refine ⟨⟨i, ⟨(xv : ℕ) - ((R.start i : ℕ+) : ℕ), by omega⟩⟩, ?_⟩
    refine Subtype.ext ?_
    show runVertex (R.start i) ((xv : ℕ) - ((R.start i : ℕ+) : ℕ)) = x
    rw [hxv]
    refine PNat.coe_injective ?_
    show ((R.start i : ℕ+) : ℕ) + ((xv : ℕ) - ((R.start i : ℕ+) : ℕ)) = (xv : ℕ)
    omega

theorem supportEquiv_apply (p : Σ i : Fin n, Fin (R.len i)) :
    ((R.supportEquiv p : (R.support : Set ℕ+)) : ℕ+)
      = runVertex (R.start p.1) (p.2 : ℕ) := rfl

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

/-! ## The E289 state carried by a run family -/

/-- The E289 state whose support is the vertex support of a run family, provided
every run length is an allowed component type. -/
noncomputable def toState
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes) :
    E289State where
  support := R.support
  support_finite := R.support_finite
  admissible := R.componentCardinality_mem hlen

@[simp]
theorem toState_support
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes) :
    (R.toState hlen).support = R.support := rfl

/-- The reciprocal value of the state of a run family is the sum of the
reciprocal weights of its run vertices. -/
theorem reciprocalValue_toState
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes) :
    reciprocalValue (R.toState hlen)
      = ∑ i : Fin n, ∑ j : Fin (R.len i),
          reciprocalWeight (runVertex (R.start i) (j : ℕ)) := by
  classical
  have hsig : ∑ p : Σ i : Fin n, Fin (R.len i),
      reciprocalWeight (runVertex (R.start p.1) (p.2 : ℕ))
      = ∑ i : Fin n, ∑ j : Fin (R.len i),
          reciprocalWeight (runVertex (R.start i) (j : ℕ)) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  letI : Finite (R.support : Set ℕ+) := R.support_finite
  letI : Fintype (R.support : Set ℕ+) := Fintype.ofFinite _
  have hv : reciprocalValue (R.toState hlen)
      = ∑ x : (R.support : Set ℕ+), reciprocalWeight x.1 := rfl
  rw [hv, ← hsig]
  exact (Fintype.sum_equiv R.supportEquiv _ _ fun p ↦ rfl).symm

/-- The reciprocal value of the state of a run family, indexed by ranges. -/
theorem reciprocalValue_toState_range
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes) :
    reciprocalValue (R.toState hlen)
      = ∑ i : Fin n, ∑ j ∈ Finset.range (R.len i),
          reciprocalWeight (runVertex (R.start i) j) := by
  rw [reciprocalValue_toState]
  exact Finset.sum_congr rfl fun i _ ↦
    Fin.sum_univ_eq_sum_range (fun j ↦ reciprocalWeight (runVertex (R.start i) j)) (R.len i)

/-- The component profile of the state of a run family is the sum of the labels
of its run lengths. -/
theorem stateProfile_toState
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes) :
    stateProfile (R.toState hlen)
      = ∑ i : Fin n,
          Finsupp.single (⟨⟨R.len i, R.len_pos i⟩, hlen i⟩ : allowedComponentTypes) 1 := by
  classical
  letI : Finite (PiZeroObj (inducedGraph successorGraph R.support)) :=
    inferInstanceAs (Finite (R.toState hlen).Components)
  letI : Fintype (PiZeroObj (inducedGraph successorGraph R.support)) := Fintype.ofFinite _
  have hp : stateProfile (R.toState hlen)
      = ∑ c : PiZeroObj (inducedGraph successorGraph R.support),
          Finsupp.single ((R.toState hlen).componentType c) 1 := rfl
  rw [hp]
  refine (Fintype.sum_equiv R.componentEquiv.symm _ _ fun i ↦ ?_).symm
  congr 1
  exact Subtype.ext (R.componentCardinality_componentOfBlock i).symm

/-- The component profile of the state of a run family, read off from any
labelling of its runs by allowed component types. -/
theorem stateProfile_toState_eq
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes)
    (theta : Fin n → allowedComponentTypes)
    (htheta : ∀ i, (((theta i : ℕ+)) : ℕ) = R.len i) :
    stateProfile (R.toState hlen) = ∑ i : Fin n, Finsupp.single (theta i) 1 := by
  rw [stateProfile_toState]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact Subtype.ext (PNat.coe_injective (htheta i).symm)

/-- The grade of the state of a run family is its number of runs. -/
theorem grade_toState
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes) :
    grade (R.toState hlen) = n := by
  classical
  rw [grade, stateProfile_toState, map_sum]
  simp only [gradeAugmentation, componentLabelLift_single, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- A run family built from an increasing list of starts with unit gaps. -/
def ofGap (start : Fin n → ℕ+) (len : Fin n → ℕ) (hpos : ∀ i, 0 < len i)
    (hgap : ∀ i j : Fin n, i < j →
      ((start i : ℕ+) : ℕ) + len i + 1 ≤ ((start j : ℕ+) : ℕ)) : RunFamily n where
  start := start
  len := len
  len_pos := hpos
  separated := by
    intro i j hij u hu w hw
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨hw1, hw2⟩ := hw
    simp only [successorDist]
    rcases lt_or_gt_of_ne hij with h | h
    · have := hgap i j h; omega
    · have := hgap j i h; omega

@[simp] theorem ofGap_start (start : Fin n → ℕ+) (len : Fin n → ℕ) (hpos) (hgap) (i : Fin n) :
    (ofGap start len hpos hgap).start i = start i := rfl

@[simp] theorem ofGap_len (start : Fin n → ℕ+) (len : Fin n → ℕ) (hpos) (hgap) (i : Fin n) :
    (ofGap start len hpos hgap).len i = len i := rfl

/-! ## Admissibility, remoteness and lightness of a run-family state -/

/-- Separation of the blocks of a run family at any prescribed margin. -/
theorem sep_of_gap (R : RunFamily n) (s : ℕ)
    (hgap : ∀ i j : Fin n, i < j →
      ((R.start i : ℕ+) : ℕ) + R.len i + s ≤ ((R.start j : ℕ+) : ℕ)) :
    ∀ i j : Fin n, i ≠ j → ∀ u ∈ R.block i, ∀ w ∈ R.block j, s < successorDist u w := by
  intro i j hij u hu w hw
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hw1, hw2⟩ := hw
  simp only [successorDist]
  rcases lt_or_gt_of_ne hij with h | h
  · have := hgap i j h; omega
  · have := hgap j i h; omega

/-- Remoteness of a run family from a finite forbidden support. -/
theorem forb_of_large (R : RunFamily n) (c : PhysicalConstraint) (N : ℕ)
    (hN : ∀ e ∈ c.forbidden, ((e : ℕ+) : ℕ) ≤ N)
    (hstart : ∀ i : Fin n, N + c.margin + 1 ≤ ((R.start i : ℕ+) : ℕ)) :
    ∀ e ∈ c.forbidden, ∀ v : ℕ+, v ∈ R.support → c.margin < successorDist e v := by
  intro e he v hv
  obtain ⟨i, h1, h2⟩ := mem_support.1 hv
  have h3 := hN e he
  have h4 := hstart i
  simp only [successorDist]
  omega



/-- A run family whose blocks avoid the forbidden support and are pairwise
separated by more than the margin carries a `c`-admissible state. -/
theorem constraintAdmissible_toState
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes)
    (c : PhysicalConstraint)
    (hforb : ∀ e ∈ c.forbidden, ∀ v : ℕ+, v ∈ R.support → c.margin < successorDist e v)
    (hsep : ∀ i j : Fin n, i ≠ j → ∀ u ∈ R.block i, ∀ w ∈ R.block j,
      c.margin < successorDist u w) :
    ConstraintAdmissible c (R.toState hlen) := by
  refine ⟨hforb, ?_⟩
  intro u v huv
  have hne : R.index u ≠ R.index v := fun h ↦ huv (Quotient.sound (eqvGen_of_index_eq h))
  exact hsep _ _ hne _ (R.mem_block_index u) _ (R.mem_block_index v)

/-- Lightness: the reciprocal value of a run-family state is bounded by the total
run length divided by the smallest starting vertex. -/
theorem reciprocalValue_toState_le
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes)
    (m : ℕ+) (hm : ∀ i : Fin n, ((m : ℕ+) : ℕ) ≤ ((R.start i : ℕ+) : ℕ)) :
    reciprocalValue (R.toState hlen)
      ≤ (∑ i : Fin n, (R.len i : ℚ)) / (((m : ℕ+) : ℕ) : ℚ) := by
  have hdiv : (∑ i : Fin n, (R.len i : ℚ)) / ((((m : ℕ+) : ℕ)) : ℚ)
      = ∑ i : Fin n, (R.len i : ℚ) / ((((m : ℕ+) : ℕ)) : ℚ) := by
    rw [div_eq_mul_inv, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ (div_eq_mul_inv _ _).symm
  rw [reciprocalValue_toState, hdiv]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hmq : (0 : ℚ) < (((m : ℕ+) : ℕ) : ℚ) := by exact_mod_cast m.pos
  have hstep : ∀ j : Fin (R.len i),
      reciprocalWeight (runVertex (R.start i) (j : ℕ)) ≤ 1 / (((m : ℕ+) : ℕ) : ℚ) := by
    intro j
    rw [reciprocalWeight, runVertex_coe]
    refine one_div_le_one_div_of_le hmq ?_
    have := hm i
    exact_mod_cast Nat.le_trans this (Nat.le_add_right _ _)
  calc ∑ j : Fin (R.len i), reciprocalWeight (runVertex (R.start i) (j : ℕ))
      ≤ ∑ _j : Fin (R.len i), 1 / (((m : ℕ+) : ℕ) : ℚ) :=
        Finset.sum_le_sum fun j _ ↦ hstep j
    _ = (R.len i : ℚ) / (((m : ℕ+) : ℕ) : ℚ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The reciprocal value of a nonempty run-family state is positive. -/
theorem reciprocalValue_toState_pos
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes)
    (hn : 0 < n) : 0 < reciprocalValue (R.toState hlen) := by
  rw [reciprocalValue_toState]
  refine Finset.sum_pos (fun i _ ↦ ?_) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun j _ ↦ ?_) ⟨⟨0, R.len_pos i⟩, Finset.mem_univ _⟩
  rw [reciprocalWeight]
  have hpos : (0 : ℚ) < (((runVertex (R.start i) (j : ℕ) : ℕ+) : ℕ) : ℚ) := by
    exact_mod_cast (runVertex (R.start i) (j : ℕ)).pos
  exact one_div_pos.2 hpos

end RunFamily

/-! ## The component-profile group and the two neutral fibres -/

/-- The binary component type `2 ∈ Θ`. -/
def binaryType : allowedComponentTypes := ⟨2, Or.inl rfl⟩

/-- The ternary component type `3 ∈ Θ`. -/
def ternaryType : allowedComponentTypes := ⟨3, Or.inr rfl⟩

/-- The group completion `Gr(M)` of the E289 component-profile monoid. -/
abbrev E289ProfileGroup := allowedComponentTypes →₀ ℤ

/-- The canonical map `M → Gr(M)` into the group completion. -/
noncomputable def profileToGroup : E289Profile →+ E289ProfileGroup :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

/-- The generator `e₂` of `Gr(M)`. -/
noncomputable def gradeGenerator : E289ProfileGroup := Finsupp.single binaryType 1

/-- The generator `e₃` of `Gr(M)`. -/
noncomputable def defectGenerator : E289ProfileGroup := Finsupp.single ternaryType 1

/-- A neutral pair: an ordered pair of E289 states of equal reciprocal value.
This is the fibre object `Neu = (C × C) ×_Q 1₀`. -/
structure NeutralPair where
  /-- The first alternative. -/
  fst : E289State
  /-- The second alternative. -/
  snd : E289State
  /-- The two alternatives have the same reciprocal value. -/
  value_eq : reciprocalValue fst = reciprocalValue snd

/-- The component-profile difference `Δχ : Neu → Gr(M)`. -/
noncomputable def NeutralPair.profileDiff (x : NeutralPair) : E289ProfileGroup :=
  profileToGroup (stateProfile x.snd) - profileToGroup (stateProfile x.fst)

/-- The neutral grade fibre `Neu_g = Neu_{e₂}`. -/
def NeutralGradeFiber : Type := {x : NeutralPair // x.profileDiff = gradeGenerator}

/-- The neutral defect fibre `Neu_δ = Neu_{e₃-e₂}`. -/
def NeutralDefectFiber : Type :=
  {x : NeutralPair // x.profileDiff = defectGenerator - gradeGenerator}

/-- Remoteness and lightness of a neutral pair: both alternatives are
`c`-admissible and their common reciprocal mass is positive and below `b`. -/
structure RemoteLight (c : PhysicalConstraint) (b : ℚ) (x : NeutralPair) : Prop where
  /-- The first alternative is `c`-admissible. -/
  admissible_fst : ConstraintAdmissible c x.fst
  /-- The second alternative is `c`-admissible. -/
  admissible_snd : ConstraintAdmissible c x.snd
  /-- The common mass is positive. -/
  mass_pos : 0 < reciprocalValue x.fst
  /-- The common mass is below the prescribed bound. -/
  mass_lt : reciprocalValue x.fst < b

/-! ## The grade-neutral certificate

At `a = 2l+4` the sealed identity

`P(a) + P(a²+3a+1) = P(a+2) + P(a(a+3)/2) + P(a(a+3))`

reads as an identity between the reciprocal values of two explicit E289 states,
made of two and of three binary successor runs respectively. -/

/-- An explicit positive vertex. -/
def mkVertex (m : ℕ) (h : 0 < m) : ℕ+ := ⟨m, h⟩

@[simp] theorem mkVertex_coe (m : ℕ) (h : 0 < m) : ((mkVertex m h : ℕ+) : ℕ) = m := rfl

/-- Membership of a run length in the allowed component object. -/
theorem mem_allowed_of_len_eq {m : ℕ} (h : 0 < m) (hm : m = 2 ∨ m = 3) :
    (⟨m, h⟩ : ℕ+) ∈ allowedComponentTypes := by
  rcases hm with hm | hm
  · exact Or.inl (PNat.coe_injective (by simp [hm]))
  · exact Or.inr (PNat.coe_injective (by simp [hm]))

/-- The two binary runs of the left alternative of the grade-neutral identity. -/
def gradeLeftFamily (l : ℕ) : RunFamily 2 :=
  RunFamily.ofGap ![mkVertex (2 * l + 4) (by omega), mkVertex (4 * l * l + 22 * l + 29) (by positivity)]
    ![2, 2] (by intro i; fin_cases i <;> norm_num)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals nlinarith)

/-- The three binary runs of the right alternative of the grade-neutral
identity. -/
def gradeRightFamily (l : ℕ) : RunFamily 3 :=
  RunFamily.ofGap
    ![mkVertex (2 * l + 6) (by omega), mkVertex (2 * l * l + 11 * l + 14) (by positivity),
      mkVertex (4 * l * l + 22 * l + 28) (by positivity)]
    ![2, 2, 2] (by intro i; fin_cases i <;> norm_num)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals nlinarith)

theorem gradeLeft_hlen (l : ℕ) :
    ∀ i : Fin 2, (⟨(gradeLeftFamily l).len i, (gradeLeftFamily l).len_pos i⟩ : ℕ+)
      ∈ allowedComponentTypes := by
  intro i
  refine mem_allowed_of_len_eq _ (Or.inl ?_)
  fin_cases i <;> rfl

theorem gradeRight_hlen (l : ℕ) :
    ∀ i : Fin 3, (⟨(gradeRightFamily l).len i, (gradeRightFamily l).len_pos i⟩ : ℕ+)
      ∈ allowedComponentTypes := by
  intro i
  refine mem_allowed_of_len_eq _ (Or.inl ?_)
  fin_cases i <;> rfl

/-- The left alternative of the grade-neutral certificate. -/
noncomputable def gradeLeftState (l : ℕ) : E289State :=
  (gradeLeftFamily l).toState (gradeLeft_hlen l)

/-- The right alternative of the grade-neutral certificate. -/
noncomputable def gradeRightState (l : ℕ) : E289State :=
  (gradeRightFamily l).toState (gradeRight_hlen l)

theorem grade_value_eq (l : ℕ) :
    reciprocalValue (gradeLeftState l) = reciprocalValue (gradeRightState l) := by
  rw [gradeLeftState, gradeRightState,
    RunFamily.reciprocalValue_toState_range, RunFamily.reciprocalValue_toState_range]
  simp only [gradeLeftFamily, gradeRightFamily, RunFamily.ofGap_start, RunFamily.ofGap_len,
    Fin.sum_univ_two, Fin.sum_univ_three, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, reciprocalWeight, runVertex_coe, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    mkVertex_coe]
  push_cast
  have hl : (0 : ℚ) ≤ (l : ℚ) := Nat.cast_nonneg l
  have h1 : (2 * (l : ℚ) + 4) ≠ 0 := by nlinarith
  have h2 : (2 * (l : ℚ) + 5) ≠ 0 := by nlinarith
  have h3 : (4 * (l : ℚ) * l + 22 * l + 29) ≠ 0 := by nlinarith
  have h4 : (4 * (l : ℚ) * l + 22 * l + 30) ≠ 0 := by nlinarith
  have h5 : (2 * (l : ℚ) + 6) ≠ 0 := by nlinarith
  have h6 : (2 * (l : ℚ) + 7) ≠ 0 := by nlinarith
  have h7 : (2 * (l : ℚ) * l + 11 * l + 14) ≠ 0 := by nlinarith
  have h8 : (2 * (l : ℚ) * l + 11 * l + 15) ≠ 0 := by nlinarith
  have h9 : (4 * (l : ℚ) * l + 22 * l + 28) ≠ 0 := by nlinarith
  field_simp
  ring

/-! ## The defect-neutral certificate

At `a = 2l+4` and `b = a(a+2)/2 - 2 = 2l²+10l+10` the sealed identity

`P(a) + P(b) = P(a+1) + (P(b) + 1/(b+2))`

reads as an identity between the reciprocal values of two explicit E289 states,
made of two binary runs and of one binary plus one ternary run respectively. -/

/-- The two binary runs of the left alternative of the defect-neutral
identity. -/
def defectLeftFamily (l : ℕ) : RunFamily 2 :=
  RunFamily.ofGap
    ![mkVertex (2 * l + 4) (by omega), mkVertex (2 * l * l + 10 * l + 10) (by positivity)]
    ![2, 2] (by intro i; fin_cases i <;> norm_num)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals nlinarith)

/-- The binary and ternary runs of the right alternative of the defect-neutral
identity. -/
def defectRightFamily (l : ℕ) : RunFamily 2 :=
  RunFamily.ofGap
    ![mkVertex (2 * l + 5) (by omega), mkVertex (2 * l * l + 10 * l + 10) (by positivity)]
    ![2, 3] (by intro i; fin_cases i <;> norm_num)
    (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
      all_goals nlinarith)

theorem defectLeft_hlen (l : ℕ) :
    ∀ i : Fin 2, (⟨(defectLeftFamily l).len i, (defectLeftFamily l).len_pos i⟩ : ℕ+)
      ∈ allowedComponentTypes := by
  intro i
  refine mem_allowed_of_len_eq _ (Or.inl ?_)
  fin_cases i <;> rfl

theorem defectRight_hlen (l : ℕ) :
    ∀ i : Fin 2, (⟨(defectRightFamily l).len i, (defectRightFamily l).len_pos i⟩ : ℕ+)
      ∈ allowedComponentTypes := by
  intro i
  fin_cases i
  · exact mem_allowed_of_len_eq _ (Or.inl rfl)
  · exact mem_allowed_of_len_eq _ (Or.inr rfl)

/-- The left alternative of the defect-neutral certificate. -/
noncomputable def defectLeftState (l : ℕ) : E289State :=
  (defectLeftFamily l).toState (defectLeft_hlen l)

/-- The right alternative of the defect-neutral certificate. -/
noncomputable def defectRightState (l : ℕ) : E289State :=
  (defectRightFamily l).toState (defectRight_hlen l)

theorem defect_value_eq (l : ℕ) :
    reciprocalValue (defectLeftState l) = reciprocalValue (defectRightState l) := by
  rw [defectLeftState, defectRightState,
    RunFamily.reciprocalValue_toState_range, RunFamily.reciprocalValue_toState_range]
  simp only [defectLeftFamily, defectRightFamily, RunFamily.ofGap_start, RunFamily.ofGap_len,
    Fin.sum_univ_two, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, reciprocalWeight, runVertex_coe, Matrix.cons_val_zero, Matrix.cons_val_one,
    mkVertex_coe]
  push_cast
  have hl : (0 : ℚ) ≤ (l : ℚ) := Nat.cast_nonneg l
  have h1 : (2 * (l : ℚ) + 4) ≠ 0 := by nlinarith
  have h2 : (2 * (l : ℚ) + 5) ≠ 0 := by nlinarith
  have h3 : (2 * (l : ℚ) + 6) ≠ 0 := by nlinarith
  have h4 : (2 * (l : ℚ) * l + 10 * l + 10) ≠ 0 := by nlinarith
  have h5 : (2 * (l : ℚ) * l + 10 * l + 11) ≠ 0 := by nlinarith
  have h6 : (2 * (l : ℚ) * l + 10 * l + 12) ≠ 0 := by nlinarith
  field_simp
  ring

/-! ## Component profiles of the four certificate states -/

theorem profileToGroup_single (theta : allowedComponentTypes) :
    profileToGroup (Finsupp.single theta 1) = Finsupp.single theta 1 := by
  simp [profileToGroup]

theorem stateProfile_gradeLeft (l : ℕ) :
    stateProfile (gradeLeftState l) = 2 • Finsupp.single binaryType 1 := by
  rw [gradeLeftState,
    RunFamily.stateProfile_toState_eq _ _ (fun _ ↦ binaryType) (by intro i; fin_cases i <;> rfl)]
  simp [Finset.sum_const]

theorem stateProfile_gradeRight (l : ℕ) :
    stateProfile (gradeRightState l) = 3 • Finsupp.single binaryType 1 := by
  rw [gradeRightState,
    RunFamily.stateProfile_toState_eq _ _ (fun _ ↦ binaryType) (by intro i; fin_cases i <;> rfl)]
  simp [Finset.sum_const]

theorem stateProfile_defectLeft (l : ℕ) :
    stateProfile (defectLeftState l) = 2 • Finsupp.single binaryType 1 := by
  rw [defectLeftState,
    RunFamily.stateProfile_toState_eq _ _ (fun _ ↦ binaryType) (by intro i; fin_cases i <;> rfl)]
  simp [Finset.sum_const]

theorem stateProfile_defectRight (l : ℕ) :
    stateProfile (defectRightState l)
      = Finsupp.single binaryType 1 + Finsupp.single ternaryType 1 := by
  rw [defectRightState,
    RunFamily.stateProfile_toState_eq _ _ ![binaryType, ternaryType]
      (by intro i; fin_cases i <;> rfl)]
  simp [Fin.sum_univ_two]

/-! ## The remote-light regular-epimorphism theorem -/

theorem gradeLeft_start_ge (l t : ℕ) (ht : t ≤ l) :
    ∀ i : Fin 2, t + 1 ≤ (((gradeLeftFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [gradeLeftFamily]
  all_goals nlinarith

theorem gradeLeft_gap (l s : ℕ) (hs : s ≤ l) :
    ∀ i j : Fin 2, i < j →
      (((gradeLeftFamily l).start i : ℕ+) : ℕ) + (gradeLeftFamily l).len i + s
        ≤ (((gradeLeftFamily l).start j : ℕ+) : ℕ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [gradeLeftFamily]
  all_goals nlinarith

theorem gradeLeft_min (l : ℕ) :
    ∀ i : Fin 2, 2 * l + 4 ≤ (((gradeLeftFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [gradeLeftFamily]
  all_goals nlinarith

theorem gradeLeft_lenSum (l : ℕ) :
    (∑ i : Fin 2, ((gradeLeftFamily l).len i : ℚ)) = 4 := by
  simp [gradeLeftFamily, Fin.sum_univ_two]
  norm_num

theorem gradeRight_start_ge (l t : ℕ) (ht : t ≤ l) :
    ∀ i : Fin 3, t + 1 ≤ (((gradeRightFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [gradeRightFamily]
  all_goals nlinarith

theorem gradeRight_gap (l s : ℕ) (hs : s ≤ l) :
    ∀ i j : Fin 3, i < j →
      (((gradeRightFamily l).start i : ℕ+) : ℕ) + (gradeRightFamily l).len i + s
        ≤ (((gradeRightFamily l).start j : ℕ+) : ℕ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [gradeRightFamily]
  all_goals nlinarith

theorem gradeRight_min (l : ℕ) :
    ∀ i : Fin 3, 2 * l + 4 ≤ (((gradeRightFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [gradeRightFamily]
  all_goals nlinarith

theorem gradeRight_lenSum (l : ℕ) :
    (∑ i : Fin 3, ((gradeRightFamily l).len i : ℚ)) = 6 := by
  simp [gradeRightFamily, Fin.sum_univ_three]
  norm_num

theorem defectLeft_start_ge (l t : ℕ) (ht : t ≤ l) :
    ∀ i : Fin 2, t + 1 ≤ (((defectLeftFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [defectLeftFamily]
  all_goals nlinarith

theorem defectLeft_gap (l s : ℕ) (hs : s ≤ l) :
    ∀ i j : Fin 2, i < j →
      (((defectLeftFamily l).start i : ℕ+) : ℕ) + (defectLeftFamily l).len i + s
        ≤ (((defectLeftFamily l).start j : ℕ+) : ℕ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [defectLeftFamily]
  all_goals nlinarith

theorem defectLeft_min (l : ℕ) :
    ∀ i : Fin 2, 2 * l + 4 ≤ (((defectLeftFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [defectLeftFamily]
  all_goals nlinarith

theorem defectLeft_lenSum (l : ℕ) :
    (∑ i : Fin 2, ((defectLeftFamily l).len i : ℚ)) = 4 := by
  simp [defectLeftFamily, Fin.sum_univ_two]
  norm_num

theorem defectRight_start_ge (l t : ℕ) (ht : t ≤ l) :
    ∀ i : Fin 2, t + 1 ≤ (((defectRightFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [defectRightFamily]
  all_goals nlinarith

theorem defectRight_gap (l s : ℕ) (hs : s ≤ l) :
    ∀ i j : Fin 2, i < j →
      (((defectRightFamily l).start i : ℕ+) : ℕ) + (defectRightFamily l).len i + s
        ≤ (((defectRightFamily l).start j : ℕ+) : ℕ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [defectRightFamily]
  all_goals nlinarith

theorem defectRight_min (l : ℕ) :
    ∀ i : Fin 2, 2 * l + 4 ≤ (((defectRightFamily l).start i : ℕ+) : ℕ) := by
  intro i
  fin_cases i <;> simp_all [defectRightFamily]
  all_goals nlinarith

theorem defectRight_lenSum (l : ℕ) :
    (∑ i : Fin 2, ((defectRightFamily l).len i : ℚ)) = 5 := by
  simp [defectRightFamily, Fin.sum_univ_two]
  norm_num

/-- Admissibility, positivity and lightness of the state of a run family that is
remote from a finite constraint and separated beyond its margin. -/
private theorem remoteLight_of_family {n : ℕ} (R : RunFamily n)
    (hlen : ∀ i : Fin n, (⟨R.len i, R.len_pos i⟩ : ℕ+) ∈ allowedComponentTypes)
    (hn : 0 < n) (c : PhysicalConstraint) (bd : ℚ) (N : ℕ)
    (hN : ∀ e ∈ c.forbidden, ((e : ℕ+) : ℕ) ≤ N)
    (hstart : ∀ i, N + c.margin + 1 ≤ ((R.start i : ℕ+) : ℕ))
    (hgap : ∀ i j : Fin n, i < j →
      ((R.start i : ℕ+) : ℕ) + R.len i + c.margin ≤ ((R.start j : ℕ+) : ℕ))
    (m : ℕ+) (hm : ∀ i, ((m : ℕ+) : ℕ) ≤ ((R.start i : ℕ+) : ℕ))
    (hbd : (∑ i : Fin n, (R.len i : ℚ)) / ((((m : ℕ+) : ℕ)) : ℚ) < bd) :
    ConstraintAdmissible c (R.toState hlen) ∧
      0 < reciprocalValue (R.toState hlen) ∧ reciprocalValue (R.toState hlen) < bd :=
  ⟨R.constraintAdmissible_toState hlen c (RunFamily.forb_of_large R c N hN hstart)
      (RunFamily.sep_of_gap R c.margin hgap),
    R.reciprocalValue_toState_pos hlen hn,
    lt_of_le_of_lt (R.reciprocalValue_toState_le hlen m hm) hbd⟩

theorem grade_profileDiff (l : ℕ) :
    (⟨gradeLeftState l, gradeRightState l, grade_value_eq l⟩ :
      NeutralPair).profileDiff = gradeGenerator := by
  show profileToGroup (stateProfile (gradeRightState l))
      - profileToGroup (stateProfile (gradeLeftState l)) = gradeGenerator
  rw [stateProfile_gradeLeft, stateProfile_gradeRight, map_nsmul, map_nsmul,
    profileToGroup_single, gradeGenerator]
  abel

theorem defect_profileDiff (l : ℕ) :
    (⟨defectLeftState l, defectRightState l, defect_value_eq l⟩ :
      NeutralPair).profileDiff = defectGenerator - gradeGenerator := by
  show profileToGroup (stateProfile (defectRightState l))
      - profileToGroup (stateProfile (defectLeftState l))
    = defectGenerator - gradeGenerator
  rw [stateProfile_defectLeft, stateProfile_defectRight, map_nsmul, map_add,
    profileToGroup_single, profileToGroup_single, gradeGenerator, defectGenerator]
  abel

/-- N.1–N.4: for every finite physical constraint and every positive common-mass
bound, the constrained light subobjects of both neutral fibres are inhabited —
that is, their projections to the terminal object are regular epimorphisms in
the frozen `Type` setting — with component-profile strata `(2e₂, 3e₂)` and
`(2e₂, e₂+e₃)` respectively. -/
theorem neutralFibres_remote_light (c : PhysicalConstraint) (bd : ℚ) (hbd : 0 < bd) :
    Nonempty {x : NeutralGradeFiber //
        RemoteLight c bd x.1 ∧
          stateProfile x.1.fst = 2 • Finsupp.single binaryType 1 ∧
          stateProfile x.1.snd = 3 • Finsupp.single binaryType 1} ∧
      Nonempty {x : NeutralDefectFiber //
        RemoteLight c bd x.1 ∧
          stateProfile x.1.fst = 2 • Finsupp.single binaryType 1 ∧
          stateProfile x.1.snd =
            Finsupp.single binaryType 1 + Finsupp.single ternaryType 1} := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ e ∈ c.forbidden, ((e : ℕ+) : ℕ) ≤ N :=
    ⟨c.forbidden.sup fun e ↦ ((e : ℕ+) : ℕ), fun e he ↦ Finset.le_sup he⟩
  obtain ⟨M, hM⟩ := exists_nat_gt ((3 : ℚ) / bd)
  obtain ⟨l, hlN, hlM⟩ : ∃ l : ℕ, N + c.margin ≤ l ∧ M ≤ l :=
    ⟨max (N + c.margin) M, le_max_left _ _, le_max_right _ _⟩
  have hlq : (0 : ℚ) ≤ (l : ℚ) := Nat.cast_nonneg l
  have hden : (0 : ℚ) < 2 * (l : ℚ) + 4 := by nlinarith
  have hMl : (M : ℚ) ≤ (l : ℚ) := by exact_mod_cast hlM
  have h3 : (3 : ℚ) < (M : ℚ) * bd := (div_lt_iff₀ hbd).1 hM
  have h6 : (6 : ℚ) < bd * (2 * (l : ℚ) + 4) := by nlinarith
  have hmpos : 0 < 2 * l + 4 := by omega
  have hslN : c.margin ≤ l := le_trans (Nat.le_add_left _ _) hlN
  have hlight : ∀ t : ℚ, t ≤ 6 →
      t / ((((mkVertex (2 * l + 4) hmpos : ℕ+) : ℕ)) : ℚ) < bd := by
    intro t ht
    rw [mkVertex_coe]
    push_cast
    rw [div_lt_iff₀ hden]
    linarith
  have hGL := remoteLight_of_family (gradeLeftFamily l) (gradeLeft_hlen l) (by norm_num) c bd N hN
    (gradeLeft_start_ge l (N + c.margin) hlN) (gradeLeft_gap l c.margin hslN)
    (mkVertex (2 * l + 4) hmpos)
    (by intro i; rw [mkVertex_coe]; exact gradeLeft_min l i)
    (by rw [gradeLeft_lenSum]; exact hlight 4 (by norm_num))
  have hGR := remoteLight_of_family (gradeRightFamily l) (gradeRight_hlen l) (by norm_num) c bd N hN
    (gradeRight_start_ge l (N + c.margin) hlN) (gradeRight_gap l c.margin hslN)
    (mkVertex (2 * l + 4) hmpos)
    (by intro i; rw [mkVertex_coe]; exact gradeRight_min l i)
    (by rw [gradeRight_lenSum]; exact hlight 6 (by norm_num))
  have hDL := remoteLight_of_family (defectLeftFamily l) (defectLeft_hlen l) (by norm_num) c bd N hN
    (defectLeft_start_ge l (N + c.margin) hlN) (defectLeft_gap l c.margin hslN)
    (mkVertex (2 * l + 4) hmpos)
    (by intro i; rw [mkVertex_coe]; exact defectLeft_min l i)
    (by rw [defectLeft_lenSum]; exact hlight 4 (by norm_num))
  have hDR := remoteLight_of_family (defectRightFamily l) (defectRight_hlen l) (by norm_num) c bd N
    hN (defectRight_start_ge l (N + c.margin) hlN) (defectRight_gap l c.margin hslN)
    (mkVertex (2 * l + 4) hmpos)
    (by intro i; rw [mkVertex_coe]; exact defectRight_min l i)
    (by rw [defectRight_lenSum]; exact hlight 5 (by norm_num))
  refine ⟨⟨⟨⟨⟨gradeLeftState l, gradeRightState l, grade_value_eq l⟩, grade_profileDiff l⟩,
      ⟨⟨hGL.1, hGR.1, hGL.2.1, hGL.2.2⟩,
        stateProfile_gradeLeft l, stateProfile_gradeRight l⟩⟩⟩,
    ⟨⟨⟨⟨defectLeftState l, defectRightState l, defect_value_eq l⟩, defect_profileDiff l⟩,
      ⟨⟨hDL.1, hDR.1, hDL.2.1, hDL.2.2⟩,
        stateProfile_defectLeft l, stateProfile_defectRight l⟩⟩⟩⟩

end Erdos289
