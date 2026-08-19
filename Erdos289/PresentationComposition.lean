module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.ProviderInterfaces
public import Erdos289.BinaryBlocks
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Rat

@[expose] public section

/-!
# Cofinal composition of reciprocal presentations

Finite presentation fibres compose after enlarging the next compact physical
constraint. The public operation is union in the reciprocal-fold fibre; the
initial-segment obstacle below is only its path-specific Lean realization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Erdos289

def positiveSucc (k : ℕ) : Denominator := ⟨k + 1, by omega⟩

/-- The denominators at most `N`.  The object means exactly the cutoff it
names: `n ∈ denominatorPrefix N ↔ n ≤ N`. -/
def denominatorPrefix (N : ℕ) : Support :=
  (Finset.range N).image positiveSucc

@[simp] theorem mem_denominatorPrefix {N : ℕ} {n : Denominator} :
    n ∈ denominatorPrefix N ↔ n.1 ≤ N := by
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    simp only [Finset.mem_range] at hk
    simp only [positiveSucc]
    omega
  · intro hn
    change n ∈ (Finset.range N).image positiveSucc
    rw [Finset.mem_image]
    have hpos := n.2
    refine ⟨n.1 - 1, by simp only [Finset.mem_range]; omega, ?_⟩
    apply Subtype.ext
    simp only [positiveSucc]
    omega

/--
The constraint a support must satisfy to be composable with `S`: it inherits
`c` and additionally forbids everything up to the last point of `S` shifted by
the effective separation margin.  That is exactly the finite lower closure the
physical union needs, and nothing more.
-/
def constraintBeyond (c : PhysicalConstraint) (S : Support) : PhysicalConstraint where
  obstacle := c.obstacle ∪
    denominatorPrefix (S.sup fun n => n.1 + max 1 c.separation)
  separation := c.separation

theorem mem_constraintBeyond_of_mem_prefix (c : PhysicalConstraint) (S : Support)
    {n : Denominator}
    (hn : n ∈ denominatorPrefix (S.sup fun x => x.1 + max 1 c.separation)) :
    n ∈ (constraintBeyond c S).obstacle := by
  simp [constraintBeyond, hn]

theorem separated_union_of_avoids_beyond
    (c : PhysicalConstraint) {S T : Support}
    (hS : S.PointSeparated c.separation)
    (hT : T.PointSeparated c.separation)
    (havoid : T.Avoids (constraintBeyond c S)) :
    (S ∪ T).PointSeparated c.separation := by
  intro a ha b hb hab
  rcases Finset.mem_union.mp ha with haS | haT <;>
    rcases Finset.mem_union.mp hb with hbS | hbT
  · exact hS a haS b hbS hab
  · have hale : a.1 + max 1 c.separation ≤ S.sup fun x => x.1 + max 1 c.separation :=
      Finset.le_sup (f := fun x : Denominator => x.1 + max 1 c.separation) haS
    have hbnot : b ∉ denominatorPrefix (S.sup fun x => x.1 + max 1 c.separation) := by
      intro hbp
      exact (Finset.disjoint_left.mp havoid hbT)
        (mem_constraintBeyond_of_mem_prefix c S hbp)
    rw [mem_denominatorPrefix] at hbnot
    rw [Nat.dist_eq_sub_of_le (by omega)]
    omega
  · rw [Nat.dist_comm]
    have hble : b.1 + max 1 c.separation ≤ S.sup fun x => x.1 + max 1 c.separation :=
      Finset.le_sup (f := fun x : Denominator => x.1 + max 1 c.separation) hbS
    have hanot : a ∉ denominatorPrefix (S.sup fun x => x.1 + max 1 c.separation) := by
      intro hap
      exact (Finset.disjoint_left.mp havoid haT)
        (mem_constraintBeyond_of_mem_prefix c S hap)
    rw [mem_denominatorPrefix] at hanot
    rw [Nat.dist_eq_sub_of_le (by omega)]
    omega
  · exact hT a haT b hbT hab

/-- The empty support is the zero point of every constrained presentation fibre. -/
def RationalPresentation.zero (c : PhysicalConstraint) :
    RationalPresentation 0 c where
  support := ∅
  value_eq := Support.value_empty
  avoids := by
    change Disjoint ∅ c.obstacle
    exact Finset.disjoint_empty_left c.obstacle
  pointSeparated := by simp [Support.PointSeparated]

theorem support_disjoint_of_avoids_beyond
    (c : PhysicalConstraint) {S T : Support}
    (havoid : T.Avoids (constraintBeyond c S)) :
    Disjoint S T := by
  rw [Finset.disjoint_left]
  intro x hxS hxT
  have hxle : x.1 + max 1 c.separation ≤
      S.sup fun y => y.1 + max 1 c.separation :=
    Finset.le_sup (f := fun y : Denominator => y.1 + max 1 c.separation) hxS
  have hxprefix : x ∈ denominatorPrefix
      (S.sup fun y => y.1 + max 1 c.separation) := by
    rw [mem_denominatorPrefix]
    omega
  exact (Finset.disjoint_left.mp havoid hxT)
    (mem_constraintBeyond_of_mem_prefix c S hxprefix)

theorem avoids_of_avoids_beyond
    (c : PhysicalConstraint) {S T : Support}
    (havoid : T.Avoids (constraintBeyond c S)) :
    T.Avoids c := by
  rw [Support.Avoids, Finset.disjoint_left]
  intro x hxT hxc
  exact (Finset.disjoint_left.mp havoid hxT) (by
    simp [constraintBeyond, hxc])

theorem crossSeparated_of_avoids_beyond
    (c : PhysicalConstraint) {S T : Support}
    (havoid : T.Avoids (constraintBeyond c S)) :
    S.CrossSeparated T (max 1 c.separation) := by
  intro x hxS y hyT
  have hxle : x.1 + max 1 c.separation ≤
      S.sup fun z => z.1 + max 1 c.separation :=
    Finset.le_sup (f := fun z : Denominator => z.1 + max 1 c.separation) hxS
  have hynot : y ∉ denominatorPrefix
      (S.sup fun z => z.1 + max 1 c.separation) := by
    intro hyp
    exact (Finset.disjoint_left.mp havoid hyT)
      (mem_constraintBeyond_of_mem_prefix c S hyp)
  rw [mem_denominatorPrefix] at hynot
  rw [Nat.dist_eq_sub_of_le (by omega)]
  omega

theorem admissible_of_admissible_beyond
    {L : Set ℕ} (c : PhysicalConstraint) {S T : Support}
    (hT : T.Admissible L (constraintBeyond c S)) :
    T.Admissible L c := by
  exact ⟨hT.1, avoids_of_avoids_beyond c hT.2.1, hT.2.2⟩

/-- Admissible supports compose canonically after moving the second beyond the first. -/
theorem Support.admissible_unionBeyond
    {L : Set ℕ} (c : PhysicalConstraint) {S T : Support}
    (hS : S.Admissible L c)
    (hT : T.Admissible L (constraintBeyond c S)) :
    (S ∪ T).Admissible L c := by
  have hcross := crossSeparated_of_avoids_beyond c hT.2.1
  exact Support.admissible_union
    (crossSeparated_graphDisjoint
      (crossSeparated_mono hcross (Nat.le_max_left 1 c.separation)))
    (crossSeparated_mono hcross (Nat.le_max_right 1 c.separation))
    hS (admissible_of_admissible_beyond c hT)

/-- Union is the canonical fibrewise sum once the second point is beyond the first. -/
def RationalPresentation.unionBeyond
    {q r : ℚ} {c : PhysicalConstraint}
    (x : RationalPresentation q c)
    (y : RationalPresentation r (constraintBeyond c x.support)) :
    RationalPresentation (q + r) c where
  support := x.support ∪ y.support
  value_eq := by
    rw [Support.value_union
      (support_disjoint_of_avoids_beyond c y.avoids), x.value_eq, y.value_eq]
  avoids := by
    rw [Support.Avoids, Finset.disjoint_left]
    intro z hz hzc
    rcases Finset.mem_union.mp hz with hzx | hzy
    · exact (Finset.disjoint_left.mp x.avoids hzx) hzc
    · exact (Finset.disjoint_left.mp (avoids_of_avoids_beyond c y.avoids) hzy) hzc
  pointSeparated := separated_union_of_avoids_beyond c
    x.pointSeparated y.pointSeparated y.avoids

/-- Cofinality for unit fractions formally supplies every finite natural multiple. -/
theorem rationalPresentation_natMultiple
    (hE : UnitFractionRefinementCofinality)
    (k : ℕ) (n : Denominator) (c : PhysicalConstraint) :
    Nonempty (RationalPresentation ((k : ℚ) * reciprocal n) c) := by
  induction k with
  | zero =>
      simpa using Nonempty.intro (RationalPresentation.zero c)
  | succ k ih =>
      obtain ⟨x⟩ := ih
      obtain ⟨y⟩ := hE n (constraintBeyond c x.support)
      have hxy := x.unionBeyond y.toRational
      simpa [Nat.cast_succ, add_mul] using Nonempty.intro hxy

/-- The unit-fraction leaf supplies the full positive-rational presentation fibre. -/
theorem rationalPresentation_of_pos
    (hE : UnitFractionRefinementCofinality)
    (q : ℚ) (hq : 0 < q) (c : PhysicalConstraint) :
    Nonempty (RationalPresentation q c) := by
  let n : Denominator := ⟨q.den, q.den_pos⟩
  let k : ℕ := q.num.natAbs
  have hkInt : (k : ℤ) = q.num := by
    exact Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have hk : (k : ℚ) = (q.num : ℚ) := by exact_mod_cast hkInt
  obtain ⟨w⟩ := rationalPresentation_natMultiple hE k n c
  refine ⟨{
    support := w.support
    value_eq := w.value_eq.trans ?_
    avoids := w.avoids
    pointSeparated := w.pointSeparated }⟩
  rw [hk]
  simp only [n, reciprocal]
  rw [← mul_div_assoc, mul_one, Rat.num_div_den]

end Erdos289
