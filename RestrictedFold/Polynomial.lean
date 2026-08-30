import RestrictedFold.Basic

import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp

/-!
# Leaf RF — the polynomial toolkit

The finite-grid coefficient detector (RF.1), the universal Vandermonde
alternation and its coefficient formula (RF.2, RF.3), and the fixed-sum exponent
constructor (RF.4).
-/

open scoped BigOperators

namespace Erdos289

/-! ## RF.1 — the finite-grid coefficient detector -/

/-- RF.1: a multivariate polynomial of total degree at most `t.degree` with a
nonzero coefficient at `t` cannot vanish on a finite grid whose `i`-th side has
more than `t i` points. -/
theorem gridDetector {σ R : Type*} [CommRing R] [IsDomain R] [Finite σ]
    (f : MvPolynomial σ R) (t : σ →₀ ℕ) (ht : MvPolynomial.coeff t f ≠ 0)
    (hdeg : f.totalDegree ≤ t.degree) (S : σ → Finset R) (hS : ∀ i, t i < (S i).card) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ MvPolynomial.eval s f ≠ 0 :=
  MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero f t ht
    (le_antisymm hdeg (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 ht))) S hS

/-! ## RF.2 — the universal alternation -/

/-- The falling-factorial matrix of a tuple of natural numbers. -/
def descFactorialMatrix {h : ℕ} (k : Fin h → ℕ) : Matrix (Fin h) (Fin h) ℤ :=
  Matrix.of fun i j ↦ ((k i).descFactorial (j : ℕ) : ℤ)

/-- The unitriangular change of basis from falling factorials to powers. -/
private noncomputable def descPochhammerMatrix (h : ℕ) : Matrix (Fin h) (Fin h) ℤ :=
  Matrix.of fun l j ↦ (descPochhammer ℤ (j : ℕ)).coeff (l : ℕ)

private theorem descFactorialMatrix_eq {h : ℕ} (k : Fin h → ℕ) :
    descFactorialMatrix k
      = Matrix.vandermonde (fun i ↦ ((k i : ℕ) : ℤ)) * descPochhammerMatrix h := by
  ext i j
  have hdeg : (descPochhammer ℤ (j : ℕ)).natDegree < h := by
    rw [descPochhammer_natDegree (R := ℤ)]
    exact j.2
  show ((k i).descFactorial (j : ℕ) : ℤ) = ∑ l : Fin h, ((k i : ℕ) : ℤ) ^ (l : ℕ) *
    (descPochhammer ℤ (j : ℕ)).coeff (l : ℕ)
  rw [← descPochhammer_eval_eq_descFactorial ℤ (k i) (j : ℕ),
    Polynomial.eval_eq_sum_range' hdeg, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun l _ ↦ mul_comm _ _

private theorem det_descPochhammerMatrix (h : ℕ) : (descPochhammerMatrix h).det = 1 := by
  have hupper : (descPochhammerMatrix h).IsUpperTriangular := by
    intro l j hlj
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (le_of_eq (descPochhammer_natDegree (R := ℤ) (j : ℕ))) hlj)
  rw [Matrix.det_of_isUpperTriangular hupper]
  refine Finset.prod_eq_one fun j _ ↦ ?_
  have hm := monic_descPochhammer ℤ (j : ℕ)
  have : (descPochhammer ℤ (j : ℕ)).coeff (j : ℕ)
      = (descPochhammer ℤ (j : ℕ)).leadingCoeff := by
    rw [Polynomial.leadingCoeff, descPochhammer_natDegree (R := ℤ)]
  exact this.trans hm

/-- RF.2: the falling-factorial determinant is the Vandermonde product. -/
theorem det_descFactorialMatrix {h : ℕ} (k : Fin h → ℕ) :
    (descFactorialMatrix k).det
      = ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ((k j : ℤ) - (k i : ℤ)) := by
  rw [descFactorialMatrix_eq, Matrix.det_mul, det_descPochhammerMatrix, mul_one,
    Matrix.det_vandermonde]

/-! ## RF.4 — fixed-sum exponents -/

theorem sum_fin_val (h : ℕ) : ∑ i : Fin h, (i : ℕ) = h * (h - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ i) h, Finset.sum_range_id]

/-- RF.4: for `0 ≤ m ≤ h(r-h)` there are `h` pairwise distinct exponents below
`r` whose sum is `m + h(h-1)/2`. -/
theorem exists_fixedSum_exponents (h r m : ℕ) (hh : 1 ≤ h) (hhr : h ≤ r)
    (hm : m ≤ h * (r - h)) :
    ∃ k : Fin h → ℕ, StrictMono k ∧ (∀ i, k i < r) ∧
      ∑ i : Fin h, k i = m + ∑ i : Fin h, (i : ℕ) := by
  classical
  have hsh : m % h < h := Nat.mod_lt _ hh
  have hmqs : h * (m / h) + m % h = m := Nat.div_add_mod m h
  refine ⟨fun i ↦ (i : ℕ) + m / h + (if h - m % h ≤ (i : ℕ) then 1 else 0), ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) < (b : ℕ) := hab
    show (a : ℕ) + m / h + (if h - m % h ≤ (a : ℕ) then 1 else 0)
      < (b : ℕ) + m / h + (if h - m % h ≤ (b : ℕ) then 1 else 0)
    by_cases hca : h - m % h ≤ (a : ℕ)
    · rw [if_pos hca, if_pos (le_trans hca hab'.le)]
      omega
    · rw [if_neg hca]
      split_ifs <;> omega
  · intro i
    have hi : (i : ℕ) < h := i.2
    show (i : ℕ) + m / h + (if h - m % h ≤ (i : ℕ) then 1 else 0) < r
    by_cases hc : h - m % h ≤ (i : ℕ)
    · rw [if_pos hc]
      have hs1 : 1 ≤ m % h := by omega
      have hlt : h * (m / h) < h * (r - h) := by omega
      have hq : m / h < r - h := lt_of_mul_lt_mul_left hlt (Nat.zero_le h)
      omega
    · rw [if_neg hc]
      have hle : h * (m / h) ≤ h * (r - h) := by omega
      have hq : m / h ≤ r - h := Nat.le_of_mul_le_mul_left hle hh
      omega
  · have hcount : ∑ i : Fin h, (if h - m % h ≤ (i : ℕ) then 1 else 0) = m % h := by
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ if h - m % h ≤ i then 1 else 0) h,
        Finset.sum_boole]
      have hfil : ((Finset.range h).filter fun i ↦ h - m % h ≤ i)
          = Finset.Ico (h - m % h) h := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hfil, Nat.card_Ico]
      simp only [Nat.cast_id]
      omega
    have hsplit : ∑ i : Fin h, ((i : ℕ) + m / h + (if h - m % h ≤ (i : ℕ) then 1 else 0))
        = (∑ i : Fin h, (i : ℕ)) + (∑ _i : Fin h, m / h)
          + ∑ i : Fin h, (if h - m % h ≤ (i : ℕ) then 1 else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [hsplit, hcount, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega

/-! ## RF.3 — the Vandermonde coefficient formula -/

open MvPolynomial in
/-- The universal Vandermonde alternation, as the determinant of the universal
Vandermonde matrix in the polynomial variables. -/
noncomputable def vandermondePoly (h : ℕ) : MvPolynomial (Fin h) ℤ :=
  (Matrix.vandermonde fun i ↦ (X i : MvPolynomial (Fin h) ℤ)).det

open MvPolynomial in
/-- RF.2: the universal alternation is the Vandermonde product. -/
theorem vandermondePoly_eq (h : ℕ) :
    vandermondePoly h
      = ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (X j - X i : MvPolynomial (Fin h) ℤ) :=
  Matrix.det_vandermonde _

/-- The exponent multi-index attached to a permutation. -/
noncomputable def permIndex {h : ℕ} (sigma : Equiv.Perm (Fin h)) : Fin h →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ ((sigma⁻¹ j : Fin h) : ℕ)

@[simp]
theorem permIndex_apply {h : ℕ} (sigma : Equiv.Perm (Fin h)) (j : Fin h) :
    permIndex sigma j = ((sigma⁻¹ j : Fin h) : ℕ) := rfl

theorem sum_permIndex {h : ℕ} (sigma : Equiv.Perm (Fin h)) :
    ∑ j : Fin h, (permIndex sigma) j = ∑ i : Fin h, (i : ℕ) := by
  simp only [permIndex_apply]
  exact Equiv.sum_comp sigma⁻¹ fun j ↦ (j : ℕ)

open MvPolynomial in
private theorem prod_X_pow_eq_monomial {h : ℕ} (a : Fin h → ℕ) :
    (∏ j : Fin h, (X j : MvPolynomial (Fin h) ℤ) ^ a j)
      = monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℤ) := by
  classical
  rw [MvPolynomial.monomial_eq, map_one, one_mul]
  refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
  intro j _ hj
  have hz : (Finsupp.equivFunOnFinite.symm a) j = 0 := by
    simpa using Finsupp.notMem_support_iff.1 hj
  show (X j : MvPolynomial (Fin h) ℤ) ^ a j = 1
  rw [show a j = 0 from hz, pow_zero]

open MvPolynomial in
theorem vandermondePoly_eq_sum (h : ℕ) :
    vandermondePoly h
      = ∑ sigma : Equiv.Perm (Fin h),
          C ((Equiv.Perm.sign sigma : ℤ)) * monomial (permIndex sigma) (1 : ℤ) := by
  rw [vandermondePoly, Matrix.det_apply']
  refine Finset.sum_congr rfl fun sigma _ ↦ ?_
  have hcast : ((Equiv.Perm.sign sigma : ℤ) : MvPolynomial (Fin h) ℤ)
      = C ((Equiv.Perm.sign sigma : ℤ)) :=
    (map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin h) ℤ) _).symm
  rw [hcast]
  congr 1
  have hre : (∏ i : Fin h, (X (sigma i) : MvPolynomial (Fin h) ℤ) ^ (i : ℕ))
      = ∏ j : Fin h, (X j : MvPolynomial (Fin h) ℤ) ^ ((sigma⁻¹ j : Fin h) : ℕ) := by
    have h1 : (∏ i : Fin h, (X (sigma i) : MvPolynomial (Fin h) ℤ) ^ (i : ℕ))
        = ∏ i : Fin h, (X (sigma i) : MvPolynomial (Fin h) ℤ)
            ^ ((sigma⁻¹ (sigma i) : Fin h) : ℕ) :=
      Finset.prod_congr rfl fun i _ ↦ by simp
    rw [h1]
    exact Equiv.prod_comp sigma
      fun j ↦ (X j : MvPolynomial (Fin h) ℤ) ^ ((sigma⁻¹ j : Fin h) : ℕ)
  exact hre.trans (prod_X_pow_eq_monomial _)

open MvPolynomial in
private theorem coeff_pow_mul_permMonomial {h : ℕ} (k : Fin h → ℕ) (m : ℕ)
    (hsum : ∑ i : Fin h, k i = m + ∑ i : Fin h, (i : ℕ)) (sigma : Equiv.Perm (Fin h)) :
    coeff (Finsupp.equivFunOnFinite.symm k)
        ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m
          * monomial (permIndex sigma) (1 : ℤ))
      = ((if permIndex sigma ≤ Finsupp.equivFunOnFinite.symm k then
          (Finsupp.equivFunOnFinite.symm k - permIndex sigma).multinomial else 0 : ℕ) : ℤ) := by
  classical
  rw [MvPolynomial.coeff_mul_monomial']
  split_ifs with hle
  · rw [mul_one, coeff_sum_X_pow_of_fintype]
    have hd : ∀ i : Fin h,
        (Finsupp.equivFunOnFinite.symm k - permIndex sigma) i
          = k i - ((sigma⁻¹ i : Fin h) : ℕ) := fun i ↦ by
      simp [Finsupp.tsub_apply]
    have hle' : ∀ i : Fin h, ((sigma⁻¹ i : Fin h) : ℕ) ≤ k i := fun i ↦ by
      have := Finsupp.le_def.1 hle i
      simpa using this
    have hpt : ∀ i : Fin h,
        (Finsupp.equivFunOnFinite.symm k - permIndex sigma) i
            + ((sigma⁻¹ i : Fin h) : ℕ) = k i := fun i ↦ by
      rw [hd i]
      have := hle' i
      omega
    have hsplit : ∑ i : Fin h, ((Finsupp.equivFunOnFinite.symm k - permIndex sigma) i
        + ((sigma⁻¹ i : Fin h) : ℕ)) = ∑ i : Fin h, k i :=
      Finset.sum_congr rfl fun i _ ↦ hpt i
    rw [Finset.sum_add_distrib] at hsplit
    have hinv : ∑ i : Fin h, ((sigma⁻¹ i : Fin h) : ℕ) = ∑ i : Fin h, (i : ℕ) :=
      Equiv.sum_comp sigma⁻¹ fun j ↦ (j : ℕ)
    have hsum2 : (Finsupp.equivFunOnFinite.symm k - permIndex sigma).sum (fun _ n ↦ n) = m := by
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
      omega
    rw [if_pos hsum2]
  · simp

private theorem factorial_multinomial_term {h : ℕ} (k : Fin h → ℕ) (m : ℕ)
    (hsum : ∑ i : Fin h, k i = m + ∑ i : Fin h, (i : ℕ)) (sigma : Equiv.Perm (Fin h)) :
    (∏ i : Fin h, Nat.factorial (k i)) *
        (if permIndex sigma ≤ Finsupp.equivFunOnFinite.symm k then
          (Finsupp.equivFunOnFinite.symm k - permIndex sigma).multinomial else 0)
      = Nat.factorial m * ∏ i : Fin h, ((k i).descFactorial ((sigma⁻¹ i : Fin h) : ℕ)) := by
  classical
  by_cases hle : permIndex sigma ≤ Finsupp.equivFunOnFinite.symm k
  · rw [if_pos hle]
    have hle' : ∀ i : Fin h, ((sigma⁻¹ i : Fin h) : ℕ) ≤ k i := fun i ↦ by
      have := Finsupp.le_def.1 hle i
      simpa using this
    have hd : ∀ i : Fin h,
        (Finsupp.equivFunOnFinite.symm k - permIndex sigma) i
          = k i - ((sigma⁻¹ i : Fin h) : ℕ) := fun i ↦ by
      simp [Finsupp.tsub_apply]
    have hprod : (∏ i : Fin h, Nat.factorial (k i))
        = (∏ i : Fin h, Nat.factorial ((Finsupp.equivFunOnFinite.symm k - permIndex sigma) i))
          * ∏ i : Fin h, ((k i).descFactorial ((sigma⁻¹ i : Fin h) : ℕ)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [hd i]
      exact (Nat.factorial_mul_descFactorial (hle' i)).symm
    have hmn : (Finsupp.equivFunOnFinite.symm k - permIndex sigma).multinomial
        = Nat.multinomial Finset.univ (Finsupp.equivFunOnFinite.symm k - permIndex sigma) :=
      Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)
    have hspec := Nat.multinomial_spec (Finset.univ : Finset (Fin h))
      (⇑(Finsupp.equivFunOnFinite.symm k - permIndex sigma))
    have hpt : ∀ i : Fin h,
        (Finsupp.equivFunOnFinite.symm k - permIndex sigma) i
            + ((sigma⁻¹ i : Fin h) : ℕ) = k i := fun i ↦ by
      rw [hd i]
      have := hle' i
      omega
    have hsplit : ∑ i : Fin h, ((Finsupp.equivFunOnFinite.symm k - permIndex sigma) i
        + ((sigma⁻¹ i : Fin h) : ℕ)) = ∑ i : Fin h, k i :=
      Finset.sum_congr rfl fun i _ ↦ hpt i
    rw [Finset.sum_add_distrib] at hsplit
    have hinv : ∑ i : Fin h, ((sigma⁻¹ i : Fin h) : ℕ) = ∑ i : Fin h, (i : ℕ) :=
      Equiv.sum_comp sigma⁻¹ fun j ↦ (j : ℕ)
    have hsum2 : ∑ i : Fin h, (Finsupp.equivFunOnFinite.symm k - permIndex sigma) i = m := by
      omega
    rw [hsum2] at hspec
    rw [hprod, hmn, mul_right_comm, hspec]
  · rw [if_neg hle, mul_zero]
    have : ∃ i : Fin h, k i < ((sigma⁻¹ i : Fin h) : ℕ) := by
      by_contra hc
      simp only [not_exists, not_lt] at hc
      exact hle (Finsupp.le_def.2 fun i ↦ by simpa using hc i)
    obtain ⟨i, hi⟩ := this
    have hz : ((k i).descFactorial ((sigma⁻¹ i : Fin h) : ℕ)) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.2 hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

private theorem sum_sign_descFactorial {h : ℕ} (k : Fin h → ℕ) :
    ∑ sigma : Equiv.Perm (Fin h), (Equiv.Perm.sign sigma : ℤ) *
        ((∏ i : Fin h, ((k i).descFactorial ((sigma⁻¹ i : Fin h) : ℕ)) : ℕ) : ℤ)
      = (descFactorialMatrix k).det := by
  have key : ∀ tau : Equiv.Perm (Fin h),
      ((∏ i : Fin h, ((k i).descFactorial ((tau i : Fin h) : ℕ)) : ℕ) : ℤ)
        = ∏ i : Fin h, descFactorialMatrix k i (tau i) := fun tau ↦ by
    push_cast
    rfl
  have hdet : ∑ tau : Equiv.Perm (Fin h), ((Equiv.Perm.sign tau : ℤ) *
      ((∏ i : Fin h, ((k i).descFactorial ((tau i : Fin h) : ℕ)) : ℕ) : ℤ))
      = (descFactorialMatrix k).det := by
    rw [← Matrix.det_transpose (descFactorialMatrix k), Matrix.det_apply']
    refine Finset.sum_congr rfl fun tau _ ↦ ?_
    rw [key tau]
    simp [Matrix.transpose_apply]
  rw [← hdet]
  refine Fintype.sum_bijective (fun sigma : Equiv.Perm (Fin h) ↦ sigma⁻¹)
    inv_involutive.bijective _ _ ?_
  intro sigma
  rw [Equiv.Perm.sign_inv]

open MvPolynomial in
/-- RF.3: the coefficient of `x_1^{k_1} ⋯ x_h^{k_h}` in
`(x_1 + ⋯ + x_h)^m · Vdm(x)`, in division-free form. -/
theorem vandermonde_coeff_formula {h : ℕ} (k : Fin h → ℕ) (m : ℕ)
    (hsum : ∑ i : Fin h, k i = m + ∑ i : Fin h, (i : ℕ)) :
    ((∏ i : Fin h, Nat.factorial (k i) : ℕ) : ℤ) *
        coeff (Finsupp.equivFunOnFinite.symm k)
          ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m * vandermondePoly h)
      = ((Nat.factorial m : ℕ) : ℤ)
        * ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ((k j : ℤ) - (k i : ℤ)) := by
  classical
  have hexp : coeff (Finsupp.equivFunOnFinite.symm k)
      ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m * vandermondePoly h)
      = ∑ sigma : Equiv.Perm (Fin h), (Equiv.Perm.sign sigma : ℤ) *
          ((if permIndex sigma ≤ Finsupp.equivFunOnFinite.symm k then
            (Finsupp.equivFunOnFinite.symm k - permIndex sigma).multinomial else 0 : ℕ) : ℤ) := by
    rw [vandermondePoly_eq_sum, Finset.mul_sum, coeff_sum]
    refine Finset.sum_congr rfl fun sigma _ ↦ ?_
    rw [← mul_assoc, mul_comm ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m)
      (C ((Equiv.Perm.sign sigma : ℤ))), mul_assoc, coeff_C_mul,
      coeff_pow_mul_permMonomial k m hsum sigma]
  rw [hexp, Finset.mul_sum]
  have hstep : ∀ sigma : Equiv.Perm (Fin h),
      ((∏ i : Fin h, Nat.factorial (k i) : ℕ) : ℤ) *
        ((Equiv.Perm.sign sigma : ℤ) *
          ((if permIndex sigma ≤ Finsupp.equivFunOnFinite.symm k then
            (Finsupp.equivFunOnFinite.symm k - permIndex sigma).multinomial else 0 : ℕ) : ℤ))
      = ((Nat.factorial m : ℕ) : ℤ) * ((Equiv.Perm.sign sigma : ℤ) *
          ((∏ i : Fin h, ((k i).descFactorial ((sigma⁻¹ i : Fin h) : ℕ)) : ℕ) : ℤ)) := by
    intro sigma
    have hn := factorial_multinomial_term k m hsum sigma
    have hz : ((∏ i : Fin h, Nat.factorial (k i) : ℕ) : ℤ) *
        ((if permIndex sigma ≤ Finsupp.equivFunOnFinite.symm k then
          (Finsupp.equivFunOnFinite.symm k - permIndex sigma).multinomial else 0 : ℕ) : ℤ)
        = ((Nat.factorial m : ℕ) : ℤ)
          * ((∏ i : Fin h, ((k i).descFactorial ((sigma⁻¹ i : Fin h) : ℕ)) : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun n : ℕ ↦ (n : ℤ)) hn
    rw [← mul_assoc, mul_comm ((∏ i : Fin h, Nat.factorial (k i) : ℕ) : ℤ)
      ((Equiv.Perm.sign sigma : ℤ)), mul_assoc, hz]
    ring
  rw [Finset.sum_congr rfl fun sigma _ ↦ hstep sigma, ← Finset.mul_sum,
    sum_sign_descFactorial, det_descFactorialMatrix]

open MvPolynomial in
/-- RF.3 in the sealed divided form. -/
theorem vandermonde_coeff_formula_div {h : ℕ} (k : Fin h → ℕ) (m : ℕ)
    (hsum : ∑ i : Fin h, k i = m + ∑ i : Fin h, (i : ℕ)) :
    ((coeff (Finsupp.equivFunOnFinite.symm k)
        ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m * vandermondePoly h) : ℤ) : ℚ)
      = (Nat.factorial m : ℚ) * (∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ((k j : ℚ) - (k i : ℚ)))
        / ∏ i : Fin h, (Nat.factorial (k i) : ℚ) := by
  have h0 : (∏ i : Fin h, (Nat.factorial (k i) : ℚ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ ↦ ?_
    exact_mod_cast (Nat.factorial_pos (k i)).ne'
  rw [eq_div_iff h0]
  have hq := congrArg (fun z : ℤ ↦ (z : ℚ)) (vandermonde_coeff_formula k m hsum)
  push_cast at hq
  rw [mul_comm]
  exact hq

end Erdos289
