import RestrictedFold.Basic
import RestrictedFold.Polynomial

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic

/-!
# Leaf RF — restricted-fold image growth

The image-growth theorem for the restricted additive fold on a one-dimensional
`F_p`-vector object (obligations RF.5 and RF.6).
-/

open scoped BigOperators

namespace Erdos289

open MvPolynomial

/-! ## The top-degree part of a product of affine factors -/

variable {sigma : Type*} {F : Type*} [CommRing F]

/-- The product `∏_{c ∈ s} (Y - c)` differs from `Y ^ |s|` by a polynomial of
strictly smaller degree. -/
private theorem prod_sub_C_sub_pow (Y : MvPolynomial sigma F) (hY : Y.totalDegree ≤ 1)
    (s : Finset F) :
    (∏ c ∈ s, (Y - C c)) - Y ^ s.card = 0 ∨
      ((∏ c ∈ s, (Y - C c)) - Y ^ s.card).totalDegree + 1 ≤ s.card := by
  classical
  induction s using Finset.induction with
  | empty => left; simp
  | insert a s ha ih =>
      have hcard : (insert a s).card = s.card + 1 := by
        rw [Finset.card_insert_of_notMem ha]
      have hprod : (∏ c ∈ insert a s, (Y - C c)) = (Y - C a) * ∏ c ∈ s, (Y - C c) :=
        Finset.prod_insert ha
      have hkey : (∏ c ∈ insert a s, (Y - C c)) - Y ^ (insert a s).card
          = (Y - C a) * ((∏ c ∈ s, (Y - C c)) - Y ^ s.card) - C a * Y ^ s.card := by
        rw [hprod, hcard]
        ring
      have hYa : (Y - C a).totalDegree ≤ 1 :=
        le_trans (totalDegree_sub _ _) (max_le hY (by rw [totalDegree_C]; exact Nat.zero_le 1))
      have hpow : (Y ^ s.card).totalDegree ≤ s.card :=
        le_trans (totalDegree_pow _ _) (by simpa using Nat.mul_le_mul_left s.card hY)
      have hlast : (C a * Y ^ s.card).totalDegree ≤ s.card := by
        refine le_trans (totalDegree_mul _ _) ?_
        simpa [totalDegree_C] using hpow
      rcases ih with hz | hd
      · rw [hkey, hz, mul_zero, zero_sub]
        by_cases hca : (C a : MvPolynomial sigma F) * Y ^ s.card = 0
        · left; rw [hca, neg_zero]
        · right
          rw [hcard, totalDegree_neg]
          omega
      · right
        rw [hkey, hcard]
        refine Nat.add_le_add_right ?_ 1
        refine le_trans (totalDegree_sub _ _) (max_le ?_ hlast)
        refine le_trans (totalDegree_mul _ _) ?_
        omega

/-! ## The Vandermonde alternation over a base ring -/

/-- The Vandermonde alternation over a commutative ring, by base change from the
universal one. -/
noncomputable def vandermondeOver (F : Type*) [CommRing F] (h : ℕ) :
    MvPolynomial (Fin h) F :=
  MvPolynomial.map (Int.castRingHom F) (vandermondePoly h)

theorem vandermondeOver_eq (F : Type*) [CommRing F] (h : ℕ) :
    vandermondeOver F h = ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, (X j - X i) := by
  rw [vandermondeOver, vandermondePoly_eq, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ ↦ by simp

theorem sum_card_Ioi_fin (h : ℕ) :
    ∑ i : Fin h, (Finset.Ioi i).card = ∑ i : Fin h, (i : ℕ) := by
  have hIoi : ∀ i : Fin h, (Finset.Ioi i).card = h - 1 - (i : ℕ) := fun i ↦ by
    simp [Fin.card_Ioi]
  rw [Finset.sum_congr rfl fun i _ ↦ hIoi i,
    Fin.sum_univ_eq_sum_range (fun i ↦ h - 1 - i) h,
    Fin.sum_univ_eq_sum_range (fun i ↦ i) h]
  exact Finset.sum_range_reflect (fun i ↦ i) h

theorem totalDegree_vandermondeOver (F : Type*) [CommRing F] [Nontrivial F] (h : ℕ) :
    (vandermondeOver F h).totalDegree ≤ ∑ i : Fin h, (i : ℕ) := by
  rw [vandermondeOver_eq, ← sum_card_Ioi_fin]
  refine le_trans (totalDegree_finsetProd _ _) (Finset.sum_le_sum fun i _ ↦ ?_)
  refine le_trans (totalDegree_finsetProd _ _) ?_
  have hb : ∀ j ∈ Finset.Ioi i,
      ((X j - X i : MvPolynomial (Fin h) F)).totalDegree ≤ 1 := fun j _ ↦
    le_trans (totalDegree_sub _ _)
      (max_le (le_of_eq (totalDegree_X j)) (le_of_eq (totalDegree_X i)))
  refine le_trans (Finset.sum_le_sum hb) ?_
  simp

theorem eval_vandermondeOver_eq_zero {F : Type*} [CommRing F] {h : ℕ} (s : Fin h → F)
    {a b : Fin h} (hab : a ≠ b) (hs : s a = s b) :
    eval s (vandermondeOver F h) = 0 := by
  rw [vandermondeOver_eq, eval_prod]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) ?_
    simp [hs]
  · refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_Ioi.2 hlt) ?_
    simp [hs]

/-! ## RF.5 — image growth over the prime field -/

/-- RF.5: the restricted-fold image over `F_p` grows at least like
`min {p, h(r-h)+1}`. -/
theorem restrictedFold_image_card_zmod (p : ℕ) [hp : Fact p.Prime] (A : Finset (ZMod p))
    (h : ℕ) (hh : h ≤ A.card) :
    min p (h * (A.card - h) + 1) ≤ (restrictedFoldImage h A).card := by
  classical
  have hne : NeZero p := ⟨hp.out.pos.ne'⟩
  have hpcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hrp : A.card ≤ p :=
    calc A.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ A
      _ = p := hpcard
  rcases Nat.eq_zero_or_pos h with rfl | hh1
  · have himg : restrictedFoldImage 0 A = {(0 : ZMod p)} := by
      rw [restrictedFoldImage, FinSub, Finset.powersetCard_zero]
      simp [restrictedFold]
    rw [himg, Finset.card_singleton]
    simp
  rcases eq_or_lt_of_le hh with hhr | hhr
  · have himg : restrictedFoldImage h A = {restrictedFold A} := by
      rw [restrictedFoldImage, FinSub, hhr, Finset.powersetCard_self]
      simp
    rw [himg, Finset.card_singleton, ← hhr, Nat.sub_self, Nat.mul_zero]
    exact min_le_right _ _
  -- the main case `1 ≤ h < r`
  by_contra hcon
  simp only [not_le] at hcon
  set r := A.card with hrdef
  set Cim := restrictedFoldImage h A with hCim
  set m := min (p - 1) (h * (r - h)) with hmdef
  have hpp : 2 ≤ p := hp.out.two_le
  have hCm : Cim.card ≤ m := by
    have h1 : Cim.card < p := lt_of_lt_of_le hcon (min_le_left _ _)
    have h2 : Cim.card < h * (r - h) + 1 := lt_of_lt_of_le hcon (min_le_right _ _)
    omega
  have hmlt : m < p := by omega
  obtain ⟨Cs, hCC, hCscard⟩ := Finset.exists_superset_card_eq hCm (by omega : m ≤ Fintype.card (ZMod p))
  obtain ⟨k, hkmono, hkr, hksum⟩ :=
    exists_fixedSum_exponents h r m hh1 (le_of_lt hhr) (min_le_right _ _)
  set K : Fin h →₀ ℕ := Finsupp.equivFunOnFinite.symm k with hKdef
  set Y : MvPolynomial (Fin h) (ZMod p) := ∑ i : Fin h, X i with hYdef
  set V : MvPolynomial (Fin h) (ZMod p) := vandermondeOver (ZMod p) h with hVdef
  set P : MvPolynomial (Fin h) (ZMod p) := (∏ c ∈ Cs, (Y - C c)) * V with hPdef
  -- degrees
  have hYdeg : Y.totalDegree ≤ 1 := by
    rw [hYdef]
    refine totalDegree_finsetSum_le fun i _ ↦ ?_
    exact le_of_eq (totalDegree_X i)
  have hVdeg : V.totalDegree ≤ ∑ i : Fin h, (i : ℕ) := totalDegree_vandermondeOver _ _
  have hfacdeg : (∏ c ∈ Cs, (Y - C c)).totalDegree ≤ m := by
    refine le_trans (totalDegree_finsetProd _ _) ?_
    have hb : ∀ c ∈ Cs, ((Y - C c)).totalDegree ≤ 1 := fun c _ ↦
      le_trans (totalDegree_sub _ _) (max_le hYdeg (by rw [totalDegree_C]; omega))
    refine le_trans (Finset.sum_le_sum hb) ?_
    simp [hCscard]
  have hPdeg : P.totalDegree ≤ m + ∑ i : Fin h, (i : ℕ) :=
    le_trans (totalDegree_mul _ _) (Nat.add_le_add hfacdeg hVdeg)
  have hKdeg : K.degree = m + ∑ i : Fin h, (i : ℕ) := by
    rw [Finsupp.degree_eq_sum]
    exact hksum
  -- the coefficient at `K` is the top-degree coefficient
  have hmapped : (Y ^ m * V : MvPolynomial (Fin h) (ZMod p))
      = MvPolynomial.map (Int.castRingHom (ZMod p))
          ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m * vandermondePoly h) := by
    rw [map_mul, map_pow, hVdef, vandermondeOver, hYdef, map_sum]
    simp
  have hsplit : coeff K P = coeff K (Y ^ m * V) := by
    rcases prod_sub_C_sub_pow Y hYdeg Cs with hz | hd
    · have heq : (∏ c ∈ Cs, (Y - C c)) = Y ^ Cs.card := by
        rw [← sub_eq_zero]; exact hz
      rw [hPdef, heq, hCscard]
    · have hPeq : P = Y ^ m * V + ((∏ c ∈ Cs, (Y - C c)) - Y ^ Cs.card) * V := by
        rw [hPdef, hCscard]; ring
      have hzero : coeff K (((∏ c ∈ Cs, (Y - C c)) - Y ^ Cs.card) * V) = 0 := by
        refine coeff_eq_zero_of_totalDegree_lt ?_
        rw [← Finsupp.degree_apply, hKdeg]
        refine lt_of_le_of_lt (totalDegree_mul _ _) ?_
        have hd' : ((∏ c ∈ Cs, (Y - C c)) - Y ^ Cs.card).totalDegree + 1 ≤ m := by
          rw [← hCscard]; exact hd
        omega
      rw [hPeq, coeff_add, hzero, add_zero]
  -- the coefficient is nonzero
  have hcoeffne : coeff K P ≠ 0 := by
    rw [hsplit, hmapped, coeff_map]
    intro hz
    have hRF3 := vandermonde_coeff_formula k m hksum
    have hcast := congrArg (fun z : ℤ ↦ (z : ZMod p)) hRF3
    push_cast at hcast
    rw [show ((Int.castRingHom (ZMod p))
        (coeff K ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m * vandermondePoly h)))
        = ((coeff K ((∑ i : Fin h, (X i : MvPolynomial (Fin h) ℤ)) ^ m
            * vandermondePoly h) : ℤ) : ZMod p) from rfl] at hz
    rw [hz, mul_zero] at hcast
    have hfacm : ((Nat.factorial m : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      rw [Nat.Prime.dvd_factorial hp.out]
      omega
    have hdiff : (∏ i : Fin h, ∏ j ∈ Finset.Ioi i,
        ((k j : ZMod p) - (k i : ZMod p))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun i _ ↦ Finset.prod_ne_zero_iff.2 fun j hj ↦ ?_
      have hij : i < j := Finset.mem_Ioi.1 hj
      have hkij : k i < k j := hkmono hij
      have hkjp : k j < p := lt_of_lt_of_le (hkr j) hrp
      have hkip : k i < p := lt_of_lt_of_le (hkr i) hrp
      rw [sub_ne_zero]
      intro hcc
      rw [ZMod.natCast_eq_natCast_iff'] at hcc
      rw [Nat.mod_eq_of_lt hkjp, Nat.mod_eq_of_lt hkip] at hcc
      omega
    exact (mul_ne_zero hfacm hdiff) hcast.symm
  -- the polynomial vanishes on the grid `A^h`
  have hvanish : ∀ s : Fin h → ZMod p, (∀ i, s i ∈ A) → eval s P = 0 := by
    intro s hsA
    rw [hPdef, map_mul]
    by_cases hinj : Function.Injective s
    · have hT : (Finset.univ.image s) ⊆ A := by
        intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hsA i
      have hTcard : (Finset.univ.image s).card = h := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hTsum : restrictedFold (Finset.univ.image s) = ∑ i : Fin h, s i := by
        rw [restrictedFold, Finset.sum_image fun x _ y _ hxy ↦ hinj hxy]
      have hmem : (∑ i : Fin h, s i) ∈ Cs := by
        refine hCC ?_
        rw [hCim]
        exact mem_restrictedFoldImage.2 ⟨Finset.univ.image s, hT, hTcard, hTsum⟩
      have hzero : eval s (∏ c ∈ Cs, (Y - C c)) = 0 := by
        rw [eval_prod]
        refine Finset.prod_eq_zero hmem ?_
        rw [map_sub, eval_C, hYdef, map_sum]
        simp
      rw [hzero, zero_mul]
    · obtain ⟨a, b, hab⟩ : ∃ a b : Fin h, s a = s b ∧ a ≠ b := by
        rw [Function.Injective] at hinj
        simp only [not_forall] at hinj
        obtain ⟨a, b, h1⟩ := hinj
        exact ⟨a, b, h1.1, h1.2⟩
      rw [hVdef, eval_vandermondeOver_eq_zero s hab.2 hab.1, mul_zero]
  -- contradiction with the finite-grid detector
  obtain ⟨s, hsA, hs⟩ := gridDetector P K hcoeffne (by rw [hKdeg]; exact hPdeg)
    (fun _ ↦ A) (fun i ↦ by
      show k i < A.card
      exact hkr i)
  exact hs (hvanish s hsA)

/-! ## RF.6 — basis-free descent -/

/-- RF.6: the sealed restricted-fold image-growth theorem, for a one-dimensional
`F_p`-vector object.  The bound is invariant under the frame torsor, so it
descends from the coordinate field to the intrinsic object. -/
theorem restrictedFold_image_card {p : ℕ} [Fact p.Prime] {S : Type*} [AddCommGroup S]
    [Module (ZMod p) S] [DecidableEq S] (hS : Nonempty (ZMod p ≃ₗ[ZMod p] S))
    (A : Finset S) (h : ℕ) (hh : h ≤ A.card) :
    min p (h * (A.card - h) + 1) ≤ (restrictedFoldImage h A).card := by
  classical
  obtain ⟨e⟩ := hS
  set B : Finset (ZMod p) := A.map e.symm.toAddEquiv.toEquiv.toEmbedding with hB
  have hemb : (e.symm.toAddEquiv.toEquiv.toEmbedding.trans e.toAddEquiv.toEquiv.toEmbedding)
      = Function.Embedding.refl S := by
    ext x
    simp
  have hAB : B.map e.toAddEquiv.toEquiv.toEmbedding = A := by
    rw [hB, Finset.map_map, hemb, Finset.map_refl]
  have hcardB : B.card = A.card := Finset.card_map _
  rw [← hAB, Finset.card_map, card_restrictedFoldImage_linearEquiv e h B]
  exact restrictedFold_image_card_zmod p B h (by rw [hcardB]; exact hh)

end Erdos289
