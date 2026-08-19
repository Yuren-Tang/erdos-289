module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.LocalSystem
public import Mathlib.Combinatorics.Pigeonhole

@[expose] public section

/-!
# One nonzero class and padding fill the fibre

The general mechanism for reaching a current's local target needs only *one*
nonzero class, together with class-zero states to pad the grade.  To realize
`x = j · u` at grade `h`, take `j` states of class `u` and `h - j` of class
zero: the grade is `h` and the class is `j · u`, and `j` can be taken below `p`
because a nonzero class generates a fibre of prime order.

This is weaker than asking for two distinct nonzero classes, and that matters:
at `p = 2` the fibre has a single nonzero class, so the two-class route is
unavailable, while this one still applies.  What it asks of the arithmetic is a
stock of `p - 1` states of a common nonzero class — always available by
pigeonhole once the pool is large — and `h` compatible states of class zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

/--
One nonzero class with a stock of `p - 1` states, padded by `h` states of class
zero, reaches the local target at grade `h ≥ p - 1`.
-/
theorem LocalStateSystem.coversAtGrade_of_stock_and_padding
    {Q p e : ℕ} {c : PhysicalConstraint} (L : LocalStateSystem Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    {u : PrimePowerSimpleFibre Q} (hu : u ≠ 0)
    {Su S₀ : Finset Support}
    (hSu : Su ⊆ L.atoms) (hS₀ : S₀ ⊆ L.atoms) (hdisj : Disjoint Su S₀)
    (hclassu : ∀ S ∈ Su, L.classOf S = u)
    (hclass₀ : ∀ S ∈ S₀, L.classOf S = 0)
    {h : ℕ} (hph : p - 1 ≤ h) (hcardu : p - 1 ≤ Su.card) (hcard₀ : h ≤ S₀.card)
    {maxMass : ℚ} (hmass : ∀ S ∈ L.atoms, S.value ≤ maxMass)
    (hgrade : ∀ S ∈ L.atoms, S.grade = 1) :
    L.CoversAtGrade h maxMass := by
  classical
  intro x
  obtain ⟨j, hjp, hjx⟩ := exists_lt_nsmul_of_ne_zero hp he hQ hu x
  have hjh : j ≤ h := by omega
  obtain ⟨A₁, hA₁sub, hA₁card⟩ :=
    Finset.exists_subset_card_eq (show j ≤ Su.card by omega)
  obtain ⟨A₂, hA₂sub, hA₂card⟩ :=
    Finset.exists_subset_card_eq (show h - j ≤ S₀.card by omega)
  have hAdisj : Disjoint A₁ A₂ := hdisj.mono hA₁sub hA₂sub
  have hsub : A₁ ∪ A₂ ⊆ L.atoms :=
    Finset.union_subset (hA₁sub.trans hSu) (hA₂sub.trans hS₀)
  have hpair : ((A₁ ∪ A₂ : Finset Support) : Set Support).Pairwise
      fun S T ↦ S.CompatibleFor T c := L.compatible.mono (by intro S hS; exact hsub hS)
  have hcard : (A₁ ∪ A₂).card = h := by
    rw [Finset.card_union_of_disjoint hAdisj, hA₁card, hA₂card]
    omega
  refine ⟨A₁ ∪ A₂, hsub, hcard, hpair, ?_, ?_, ?_⟩
  · rw [aggregateSupport_grade hpair,
      Finset.sum_congr rfl fun S hS => hgrade S (hsub hS)]
    simpa using hcard
  · rw [aggregateSupport_value hpair]
    calc ∑ S ∈ A₁ ∪ A₂, S.value
        ≤ ∑ _S ∈ A₁ ∪ A₂, maxMass :=
          Finset.sum_le_sum fun S hS => hmass S (hsub hS)
      _ = (h : ℚ) * maxMass := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  · intro hfac
    have hfacs : ∀ S ∈ A₁ ∪ A₂, S.FactorsThroughPrimePowerStage Q :=
      fun S hS => L.factors S (hsub hS)
    have hkey := aggregateSupport_simpleFibreClass hpair hfacs
    rw [Support.simpleFibreClass_congr hfac (aggregateSupport_factorsThrough hpair hfacs),
      hkey]
    have hterm : ∀ S : {y // y ∈ A₁ ∪ A₂},
        S.1.simpleFibreClass (hfacs S.1 S.2) = L.classOf S.1 :=
      fun S => (L.classOf_eq (hsub S.2) (hfacs S.1 S.2)).symm
    rw [Finset.sum_congr rfl fun S _ => hterm S,
      Finset.sum_attach (A₁ ∪ A₂) fun S => L.classOf S,
      Finset.sum_union hAdisj,
      Finset.sum_congr rfl fun S hS => hclassu S (hA₁sub hS),
      Finset.sum_congr rfl fun S hS => hclass₀ S (hA₂sub hS),
      Finset.sum_const, Finset.sum_const, hA₁card, hA₂card]
    simpa using hjx

open Classical in
/--
Pigeonhole on the fibre: a state system whose states all have nonzero class,
and which has more than `(p - 1) m` of them, has more than `m` states of one
common nonzero class.

The fibre has `p` elements, so `p - 1` nonzero ones; nothing else is used.
-/
theorem LocalStateSystem.exists_stock_of_card
    {Q p e : ℕ} {c : PhysicalConstraint} (L : LocalStateSystem Q c)
    (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (hnz : ∀ S ∈ L.atoms, L.classOf S ≠ 0)
    {m : ℕ} (hcard : (p - 1) * m < L.atoms.card) :
    ∃ u : PrimePowerSimpleFibre Q, u ≠ 0 ∧
      m < (L.atoms.filter fun S => L.classOf S = u).card := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set φ := primePowerSimpleFibreAddEquiv hp he hQ with hφ
  set t : Finset (ZMod p) := Finset.univ.erase 0 with ht
  have htcard : t.card = p - 1 := by
    rw [ht, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hmaps : ∀ S ∈ L.atoms, φ (L.classOf S) ∈ t := by
    intro S hS
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    intro hzero
    exact hnz S hS (φ.injective (by simpa using hzero))
  obtain ⟨y, hy, hfib⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps (by rwa [htcard])
  have hy0 : y ≠ 0 := (Finset.mem_erase.1 hy).1
  refine ⟨φ.symm y, ?_, ?_⟩
  · intro hzero
    apply hy0
    rw [← AddEquiv.apply_symm_apply φ y, hzero, map_zero]
  · have hset : (L.atoms.filter fun S => L.classOf S = φ.symm y)
        = L.atoms.filter fun S => φ (L.classOf S) = y := by
      ext S
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      constructor
      · intro hSy
        rw [hSy, AddEquiv.apply_symm_apply]
      · intro hSy
        exact φ.injective (by rw [hSy, AddEquiv.apply_symm_apply])
    rw [hset]
    exact hfib

end Erdos289
