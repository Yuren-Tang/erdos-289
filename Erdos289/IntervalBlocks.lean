module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PhysicalSupports
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

/-!
# Integer intervals as path blocks

An interval of positive integers is a connected support: its induced subgraph
in the path is a path.  This module records that, together with the block size,
the exact reciprocal value, and the separation of two intervals with a gap of
more than one.

Together with the convexity of a component proved in `Erdos289/Literal.lean`,
these are the two halves of the identification of the source problem's interval
families with the supports of the intrinsic statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- A natural number as a denominator, clamped away from zero.  The clamp never
acts on the intervals used below, all of which start at a positive endpoint. -/
def denominatorOfNat (k : ℕ) : Denominator := ⟨max 1 k, by omega⟩

@[simp]
theorem denominatorOfNat_val (k : ℕ) : (denominatorOfNat k).1 = max 1 k := rfl

/-- The support of the integer interval `[a, b]`. -/
def denominatorIcc (a b : ℕ) : Support :=
  (Finset.Icc a b).image denominatorOfNat

theorem denominatorOfNat_injOn {a b : ℕ} (ha : 0 < a) :
    Set.InjOn denominatorOfNat (Finset.Icc a b) := by
  intro x hx y hy hxy
  simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
  have := congrArg Subtype.val hxy
  rw [denominatorOfNat_val, denominatorOfNat_val] at this
  omega

theorem mem_denominatorIcc {a b : ℕ} (ha : 0 < a) {n : Denominator} :
    n ∈ denominatorIcc a b ↔ a ≤ n.1 ∧ n.1 ≤ b := by
  rw [denominatorIcc, Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Finset.mem_Icc] at hk
    rw [denominatorOfNat_val]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨n.1, Finset.mem_Icc.2 ⟨h1, h2⟩, ?_⟩
    apply Subtype.ext
    rw [denominatorOfNat_val]
    have := n.2
    omega

theorem denominatorIcc_nonempty {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (denominatorIcc a b).Nonempty :=
  ⟨⟨a, ha⟩, (mem_denominatorIcc ha).2 ⟨le_rfl, hab⟩⟩

theorem denominatorIcc_card {a b : ℕ} (ha : 0 < a) :
    (denominatorIcc a b).card = b + 1 - a := by
  classical
  rw [denominatorIcc, Finset.card_image_of_injOn (denominatorOfNat_injOn ha),
    Nat.card_Icc]

/-! ### Connectivity -/

private theorem denominatorIcc_reachable_of_shift {a b : ℕ} (ha : 0 < a) :
    ∀ (d : ℕ) (x y : {n : Denominator // n ∈ denominatorIcc a b}),
      y.1.1 = x.1.1 + d → (denominatorIcc a b).graph.Reachable x y := by
  intro d
  induction d with
  | zero =>
      intro x y h
      have : x = y := Subtype.ext (Subtype.ext (by omega))
      exact this ▸ .rfl
  | succ d ih =>
      intro x y h
      have hxmem := (mem_denominatorIcc ha).1 x.2
      have hymem := (mem_denominatorIcc ha).1 y.2
      have hzpos : 0 < x.1.1 + 1 := by omega
      have hzmem : (⟨x.1.1 + 1, hzpos⟩ : Denominator) ∈ denominatorIcc a b := by
        refine (mem_denominatorIcc ha).2 ⟨?_, ?_⟩
        · show a ≤ x.1.1 + 1
          omega
        · show x.1.1 + 1 ≤ b
          omega
      have hstep : y.1.1 = (⟨x.1.1 + 1, hzpos⟩ : Denominator).1 + d := by
        show y.1.1 = x.1.1 + 1 + d
        omega
      refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_)
        (ih ⟨⟨x.1.1 + 1, hzpos⟩, hzmem⟩ y hstep)
      change denominatorPath.Adj x.1 ⟨x.1.1 + 1, hzpos⟩
      exact Or.inl rfl

theorem denominatorIcc_preconnected {a b : ℕ} (ha : 0 < a) :
    (denominatorIcc a b).graph.Preconnected := by
  intro x y
  rcases Nat.le_total x.1.1 y.1.1 with h | h
  · exact denominatorIcc_reachable_of_shift ha (y.1.1 - x.1.1) x y (by omega)
  · exact (denominatorIcc_reachable_of_shift ha (x.1.1 - y.1.1) y x (by omega)).symm

theorem denominatorIcc_grade {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (denominatorIcc a b).grade = 1 := by
  let _ : Nonempty {n : Denominator // n ∈ denominatorIcc a b} :=
    ⟨⟨⟨a, ha⟩, (mem_denominatorIcc ha).2 ⟨le_rfl, hab⟩⟩⟩
  let _ : Subsingleton (denominatorIcc a b).Blocks :=
    (denominatorIcc_preconnected ha).subsingleton_connectedComponent
  exact Nat.card_unique

theorem denominatorIcc_blockSize {a b : ℕ} (ha : 0 < a)
    (c : (denominatorIcc a b).Blocks) :
    (denominatorIcc a b).blockSize c = b + 1 - a := by
  have hsupp : c.supp = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound
      (denominatorIcc_preconnected ha c.exists_rep.choose x)).symm.trans
        c.exists_rep.choose_spec
  rw [Support.blockSize, hsupp]
  calc
    Nat.card ↑(Set.univ : Set {n : Denominator // n ∈ denominatorIcc a b}) =
        Nat.card {n : Denominator // n ∈ denominatorIcc a b} :=
      Nat.card_congr (Equiv.Set.univ _)
    _ = Fintype.card {n : Denominator // n ∈ denominatorIcc a b} :=
      Nat.card_eq_fintype_card
    _ = (denominatorIcc a b).card := Fintype.card_coe _
    _ = b + 1 - a := denominatorIcc_card ha

theorem denominatorIcc_hasBlockSizes {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    (denominatorIcc a b).HasBlockSizes nontrivialBlockSizes := by
  intro c
  change 2 ≤ (denominatorIcc a b).blockSize c
  rw [denominatorIcc_blockSize ha]
  omega

/-- A single connected block satisfies every inter-block separation margin. -/
theorem denominatorIcc_separated {a b : ℕ} (ha : 0 < a) (margin : ℕ) :
    (denominatorIcc a b).Separated margin := by
  intro c d hcd
  let _ : Subsingleton (denominatorIcc a b).Blocks :=
    (denominatorIcc_preconnected ha).subsingleton_connectedComponent
  exact (hcd (Subsingleton.elim c d)).elim

/-- Two intervals separated by a gap of more than one are cross-separated by
one, which is the source problem's "not overlapping or adjacent". -/
theorem denominatorIcc_crossSeparated {a b a' b' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hgap : b + 1 < a') :
    (denominatorIcc a b).CrossSeparated (denominatorIcc a' b') 1 := by
  intro x hx y hy
  have hxm := (mem_denominatorIcc ha).1 hx
  have hym := (mem_denominatorIcc ha').1 hy
  simp only [Nat.dist]
  omega

/-! ### Exact value -/

theorem denominatorIcc_value {a b : ℕ} (ha : 0 < a) :
    (denominatorIcc a b).value = ∑ n ∈ Finset.Icc a b, (n : ℚ)⁻¹ := by
  classical
  rw [Support.value, denominatorIcc, Finset.sum_image]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk1 : (denominatorOfNat k).1 = k := by rw [denominatorOfNat_val]; omega
    rw [reciprocal, hk1]
    exact one_div (k : ℚ)
  · exact denominatorOfNat_injOn ha

end Erdos289
