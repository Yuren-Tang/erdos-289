import Reciprocal.CompactSubgroups

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Irreducible

/-!
# Currents, simple factors, and canonical endpoints

The intrinsic filtration of the compact-subgroup lattice of `A = ℚ/ℤ`: currents
are the nonzero join-irreducible compact stages, the lower-current stage of a
current is the join of all currents of strictly smaller rank, and the simple
factor of a current is the resulting subquotient.  The canonical endpoints are
the joins of all currents of rank at most a given bound.
-/

namespace Erdos289

set_option linter.style.haveILetI false

open CompactSubgroupStage

/-- An intrinsic current: a nonzero join-irreducible compact stage. -/
abbrev Current := {J : CompactSubgroupStage // J ≠ ⊥ ∧ SupIrred J}

namespace Current

/-- The compact subgroup underlying a current. -/
def toSubgroup (J : Current) : AddSubgroup CenteredResidueGroup := J.1.1

/-- The intrinsic rank `Q_J = |J|` of a current. -/
noncomputable def rank (J : Current) : ℕ := J.1.index

theorem rank_pos (J : Current) : 0 < J.rank := J.1.index_pos

theorem toSubgroup_eq (J : Current) : J.toSubgroup = compactSubgroupH J.rank :=
  J.1.coe_eq

theorem le_iff_rank_dvd (J K : Current) : J ≤ K ↔ J.rank ∣ K.rank :=
  CompactSubgroupStage.le_iff_index_dvd J.1 K.1

end Current

/-! ## Auxiliary compactness and arithmetic bridges -/

private theorem isPrimePow_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    IsPrimePow (p ^ k) :=
  ⟨p, k, Nat.prime_iff.1 hp, hk, rfl⟩

private theorem pow_div_self {p e : ℕ} (hp : 0 < p) (he : 1 ≤ e) :
    p ^ e / p = p ^ (e - 1) := by
  have h : p ^ e = p ^ (e - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h, Nat.mul_div_cancel _ hp]

private theorem eq_H_card {H : AddSubgroup CenteredResidueGroup}
    (hH : IsCompactElement H) : H = compactSubgroupH (Nat.card H) :=
  CompactSubgroupStage.eq_compactSubgroupH ⟨H, hH⟩

private theorem card_pos_of_compact {H : AddSubgroup CenteredResidueGroup}
    (hH : IsCompactElement H) : 0 < Nat.card H :=
  CompactSubgroupStage.index_pos ⟨H, hH⟩

private theorem isCompactElement_of_le_H {H : AddSubgroup CenteredResidueGroup}
    {N : ℕ} (hN : 0 < N) (h : H ≤ compactSubgroupH N) : IsCompactElement H := by
  haveI : Finite (compactSubgroupH N) := finite_compactSubgroupH hN
  haveI : Finite H :=
    ((Set.toFinite (↑(compactSubgroupH N) : Set CenteredResidueGroup)).subset
      (SetLike.coe_subset_coe.2 h)).to_subtype
  rw [eq_compactSubgroupH_of_finite H]
  exact isCompactElement_compactSubgroupH Nat.card_pos

private theorem primePow_dvd_lcm {p e a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : p ^ e ∣ Nat.lcm a b) : p ^ e ∣ a ∨ p ^ e ∣ b := by
  have hlcm : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  rw [hp.pow_dvd_iff_le_factorization hlcm, Nat.factorization_lcm ha hb,
    Finsupp.sup_apply] at h
  have h' : e ≤ max (a.factorization p) (b.factorization p) := h
  rcases le_max_iff.1 h' with h'' | h''
  · exact Or.inl ((hp.pow_dvd_iff_le_factorization ha).2 h'')
  · exact Or.inr ((hp.pow_dvd_iff_le_factorization hb).2 h'')

private theorem finsetSup_H (s : Finset Current) (g : Current → ℕ)
    (hg : ∀ R, 0 < g R) :
    ∃ L : ℕ, 0 < L ∧ s.sup (fun R ↦ compactSubgroupH (g R)) = compactSubgroupH L ∧
      ∀ p e : ℕ, p.Prime → 0 < e → p ^ e ∣ L → ∃ R ∈ s, p ^ e ∣ g R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, Nat.one_pos, by simp, ?_⟩
      intro p e hp he hdvd
      have h1 : p ^ e = 1 := Nat.dvd_one.1 hdvd
      have h2 : 1 < p ^ e := Nat.one_lt_pow he.ne' hp.one_lt
      omega
  | insert a s _ ih =>
      obtain ⟨L, hL, hsup, hprime⟩ := ih
      refine ⟨Nat.lcm (g a) L,
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hg a).ne' hL.ne'), ?_, ?_⟩
      · rw [Finset.sup_insert, hsup, compactSubgroupH_sup (hg a) hL]
      · intro p e hp he hdvd
        rcases primePow_dvd_lcm hp (hg a).ne' hL.ne' hdvd with h | h
        · exact ⟨a, Finset.mem_insert_self _ _, h⟩
        · obtain ⟨R, hR, hRd⟩ := hprime p e hp he h
          exact ⟨R, Finset.mem_insert_of_mem hR, hRd⟩

private theorem exists_current_of_le_iSup {J : Current} {P : Current → Prop}
    (hJ : ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ J.rank = p ^ e)
    (h : J.toSubgroup ≤ ⨆ R : Current, ⨆ _ : P R, R.toSubgroup) :
    ∃ R : Current, P R ∧ J.rank ∣ R.rank := by
  classical
  obtain ⟨p, e, hp, he, hrank⟩ := hJ
  have hJc : IsCompactElement J.toSubgroup := J.1.2
  obtain ⟨s, hs⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hJc
      (fun R : Current ↦ ⨆ _ : P R, R.toSubgroup) h
  rw [← Finset.sup_eq_iSup] at hs
  have hg : ∀ R : Current, 0 < (if P R then R.rank else 1) := by
    intro R
    by_cases hR : P R
    · simpa [hR] using R.rank_pos
    · simp [hR]
  have hbound : s.sup (fun R : Current ↦ ⨆ _ : P R, R.toSubgroup) ≤
      s.sup (fun R : Current ↦ compactSubgroupH (if P R then R.rank else 1)) := by
    refine Finset.sup_mono_fun fun R _ ↦ ?_
    by_cases hR : P R
    · rw [if_pos hR, ciSup_pos hR, R.toSubgroup_eq]
    · rw [if_neg hR, compactSubgroupH_one]
      exact iSup_le fun hc ↦ absurd hc hR
  obtain ⟨L, hL, hsup, hprime⟩ :=
    finsetSup_H s (fun R ↦ if P R then R.rank else 1) hg
  have hle : compactSubgroupH (p ^ e) ≤ compactSubgroupH L := by
    rw [← hsup, ← hrank, ← J.toSubgroup_eq]
    exact hs.trans hbound
  have hdvd : p ^ e ∣ L :=
    (compactSubgroupH_le_iff (hrank ▸ J.rank_pos)).1 hle
  obtain ⟨R, _, hRd⟩ := hprime p e hp he hdvd
  have hPR : P R := by
    by_contra hR
    rw [if_neg hR] at hRd
    have h1 : 1 < p ^ e := Nat.one_lt_pow he.ne' hp.one_lt
    have h2 := Nat.le_of_dvd Nat.one_pos hRd
    omega
  rw [if_pos hPR] at hRd
  exact ⟨R, hPR, hrank ▸ hRd⟩

/-! ## R2.1 — currents are exactly the prime-power stages -/

/-- A compact stage is a nonzero join-irreducible exactly when its index is a
prime power. -/
theorem supIrred_iff_isPrimePow (J : CompactSubgroupStage) :
    (J ≠ ⊥ ∧ SupIrred J) ↔ IsPrimePow J.index := by
  constructor
  · rintro ⟨hne, hirr⟩
    have hn1 : J.index ≠ 1 := fun h ↦ hne ((eq_bot_iff_index J).2 h)
    have hpos := J.index_pos
    by_contra hnp
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    obtain ⟨k, m, hm, hnkm⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hp.one_lt.ne'
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, pow_zero, one_mul] at hnkm
        exact absurd (hnkm ▸ hpn) hm
      · exact hk0
    have hapos : 0 < p ^ k := pow_pos hp.pos k
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · rw [hm0, mul_zero] at hnkm
        omega
      · exact hm0
    have hcop : Nat.Coprime (p ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
    have hane : p ^ k ≠ 1 := (Nat.one_lt_pow hk.ne' hp.one_lt).ne'
    have hlcm : Nat.lcm (p ^ k) m = J.index := by
      rw [Nat.Coprime.lcm_eq_mul hcop, ← hnkm]
    have hsup : ofIndex (p ^ k) hapos ⊔ ofIndex m hmpos = J := by
      apply ext_index
      rw [index_sup, index_ofIndex, index_ofIndex, hlcm]
    rcases hirr.2 hsup with h | h
    · refine hnp ⟨p, k, Nat.prime_iff.1 hp, hk, ?_⟩
      have hi := congrArg CompactSubgroupStage.index h
      rwa [index_ofIndex] at hi
    · have hi := congrArg CompactSubgroupStage.index h
      rw [index_ofIndex] at hi
      rw [← hi] at hnkm
      exact hane (Nat.eq_of_mul_eq_mul_right hmpos (by rw [one_mul]; exact hnkm.symm))
  · rintro ⟨p, e, hp, he, hpe⟩
    have hprime : p.Prime := Nat.prime_iff.2 hp
    have hne : J ≠ ⊥ := by
      intro hb
      rw [eq_bot_iff_index] at hb
      rw [hb] at hpe
      have : 1 < p ^ e := Nat.one_lt_pow he.ne' hprime.one_lt
      omega
    refine ⟨hne, ⟨fun hmin ↦ hne (isMin_iff_eq_bot.1 hmin), ?_⟩⟩
    intro B C hBC
    have hB : B.index ∣ J.index := by
      rw [← hBC, index_sup]
      exact Nat.dvd_lcm_left _ _
    have hC : C.index ∣ J.index := by
      rw [← hBC, index_sup]
      exact Nat.dvd_lcm_right _ _
    rw [← hpe] at hB hC
    obtain ⟨i, _, hBi⟩ := (Nat.dvd_prime_pow hprime).1 hB
    obtain ⟨j, _, hCj⟩ := (Nat.dvd_prime_pow hprime).1 hC
    have hlcm : Nat.lcm B.index C.index = J.index := by rw [← index_sup, hBC]
    rw [hBi, hCj] at hlcm
    rcases le_total i j with hij | hij
    · right
      apply ext_index
      rw [hCj, ← hlcm, Nat.lcm_eq_right (pow_dvd_pow p hij)]
    · left
      apply ext_index
      rw [hBi, ← hlcm, Nat.lcm_eq_left (pow_dvd_pow p hij)]

/-- R2.1: the rank of a current is a prime power. -/
theorem Current.rank_isPrimePow (J : Current) : IsPrimePow J.rank :=
  (supIrred_iff_isPrimePow J.1).1 J.2

theorem Current.exists_primePow (J : Current) :
    ∃ p e : ℕ, p.Prime ∧ 0 < e ∧ J.rank = p ^ e := by
  obtain ⟨p, e, hp, he, hpe⟩ := J.rank_isPrimePow
  exact ⟨p, e, Nat.prime_iff.2 hp, he, hpe.symm⟩

/-- The current attached to a prime power. -/
noncomputable def currentOfPrimePow (n : ℕ) (h : IsPrimePow n) : Current :=
  ⟨ofIndex n h.pos, by
    rw [supIrred_iff_isPrimePow, index_ofIndex]
    exact h⟩

@[simp]
theorem rank_currentOfPrimePow (n : ℕ) (h : IsPrimePow n) :
    (currentOfPrimePow n h).rank = n :=
  index_ofIndex n h.pos

/-- R2.1: currents correspond exactly to prime powers. -/
noncomputable def current_equiv_primePower : Current ≃ {n : ℕ // IsPrimePow n} where
  toFun J := ⟨J.rank, J.rank_isPrimePow⟩
  invFun n := currentOfPrimePow n.1 n.2
  left_inv _ := Subtype.ext (ext_index (rank_currentOfPrimePow _ _))
  right_inv _ := Subtype.ext (rank_currentOfPrimePow _ _)

/-! ## R2.2 — the lower-current stage and the current stage -/

/-- The lower-current stage `F_{<J}`: the join of all currents of strictly
smaller rank. -/
noncomputable def Flt (J : Current) : AddSubgroup CenteredResidueGroup :=
  ⨆ R : Current, ⨆ _ : R.rank < J.rank, R.toSubgroup

/-- The current stage `F_J = F_{<J} ⊔ J`. -/
noncomputable def F (J : Current) : AddSubgroup CenteredResidueGroup :=
  Flt J ⊔ J.toSubgroup

theorem Flt_le_H_factorial (J : Current) :
    Flt J ≤ compactSubgroupH (Nat.factorial J.rank) := by
  refine iSup_le fun R ↦ iSup_le fun hR ↦ ?_
  rw [R.toSubgroup_eq]
  exact compactSubgroupH_mono (Nat.dvd_factorial R.rank_pos hR.le)

theorem isCompactElement_Flt (J : Current) : IsCompactElement (Flt J) :=
  isCompactElement_of_le_H (Nat.factorial_pos _) (Flt_le_H_factorial J)

theorem isCompactElement_F (J : Current) : IsCompactElement (F J) :=
  isCompactElement_of_le_H (Nat.factorial_pos J.rank)
    (sup_le (Flt_le_H_factorial J)
      (by
        rw [J.toSubgroup_eq]
        exact compactSubgroupH_mono (Nat.dvd_factorial J.rank_pos le_rfl)))

theorem Flt_le_F (J : Current) : Flt J ≤ F J := le_sup_left

theorem le_Flt_of_rank_lt {J R : Current} (h : R.rank < J.rank) :
    R.toSubgroup ≤ Flt J :=
  le_iSup_of_le R (le_iSup_of_le h le_rfl)

/-- The lower-current stage does not already contain its current. -/
theorem not_le_Flt (J : Current) : ¬ J.toSubgroup ≤ Flt J := by
  intro h
  obtain ⟨R, hR, hdvd⟩ := exists_current_of_le_iSup J.exists_primePow h
  exact absurd (Nat.le_of_dvd R.rank_pos hdvd) (not_le.2 hR)

/-! ## R2.3 — the simple factor -/

/-- The simple factor `S_J = F_J / F_{<J}`. -/
noncomputable abbrev SimpleFactor (J : Current) :=
  (F J) ⧸ (Flt J).addSubgroupOf (F J)

/-- The nonzero part of the simple factor. -/
def NonzeroSimpleFactor (J : Current) := {x : SimpleFactor J // x ≠ 0}

/-- The order `p_J = |S_J|` of the simple factor. -/
noncomputable def simpleFactorOrder (J : Current) : ℕ := Nat.card (SimpleFactor J)

private theorem card_Flt_pos (J : Current) : 0 < Nat.card (Flt J) :=
  card_pos_of_compact (isCompactElement_Flt J)

private theorem F_eq (J : Current) :
    F J = compactSubgroupH (Nat.lcm (Nat.card (Flt J)) J.rank) := by
  have hFlt := eq_H_card (isCompactElement_Flt J)
  calc F J = Flt J ⊔ J.toSubgroup := rfl
    _ = compactSubgroupH (Nat.card (Flt J)) ⊔ compactSubgroupH J.rank := by
        rw [← hFlt, ← J.toSubgroup_eq]
    _ = compactSubgroupH (Nat.lcm (Nat.card (Flt J)) J.rank) :=
        compactSubgroupH_sup (card_Flt_pos J) J.rank_pos

private theorem card_F_eq (J : Current) :
    Nat.card (F J) = Nat.lcm (Nat.card (Flt J)) J.rank := by
  rw [F_eq J, card_compactSubgroupH]
  exact Nat.pos_of_ne_zero
    (Nat.lcm_ne_zero (card_Flt_pos J).ne' J.rank_pos.ne')

private theorem card_simpleFactor_mul (J : Current) :
    simpleFactorOrder J * Nat.card (Flt J) = Nat.card (F J) := by
  have hiso : Nat.card ((Flt J).addSubgroupOf (F J)) = Nat.card (Flt J) :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (Flt_le_F J)).toEquiv
  have h := AddSubgroup.card_mul_index ((Flt J).addSubgroupOf (F J))
  rw [AddSubgroup.index_eq_card, hiso] at h
  rw [simpleFactorOrder, mul_comm]
  exact h

private theorem primePow_valuation (J : Current) {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hrank : J.rank = p ^ e) :
    p ^ (e - 1) ∣ Nat.card (Flt J) ∧ ¬ p ^ e ∣ Nat.card (Flt J) := by
  constructor
  · rcases Nat.eq_zero_or_pos (e - 1) with h | h
    · rw [h, pow_zero]
      exact one_dvd _
    · have hpp : IsPrimePow (p ^ (e - 1)) := ⟨p, e - 1, Nat.prime_iff.1 hp, h, rfl⟩
      have hRrank : (currentOfPrimePow (p ^ (e - 1)) hpp).rank = p ^ (e - 1) :=
        rank_currentOfPrimePow _ _
      have hlt : (currentOfPrimePow (p ^ (e - 1)) hpp).rank < J.rank := by
        rw [hRrank, hrank]
        exact Nat.pow_lt_pow_right hp.one_lt (by omega)
      have hle := le_Flt_of_rank_lt hlt
      rw [(currentOfPrimePow (p ^ (e - 1)) hpp).toSubgroup_eq, hRrank,
        eq_H_card (isCompactElement_Flt J)] at hle
      exact (compactSubgroupH_le_iff (pow_pos hp.pos _)).1 hle
  · intro hdvd
    apply not_le_Flt J
    have hmono := compactSubgroupH_mono hdvd
    rw [← eq_H_card (isCompactElement_Flt J)] at hmono
    rw [J.toSubgroup_eq, hrank]
    exact hmono

private theorem lcm_of_valuation {m p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hdvd : p ^ (e - 1) ∣ m) (hndvd : ¬ p ^ e ∣ m) :
    Nat.lcm m (p ^ e) = m * p := by
  have hgcd : Nat.gcd m (p ^ e) = p ^ (e - 1) := by
    have hle : p ^ (e - 1) ∣ Nat.gcd m (p ^ e) :=
      Nat.dvd_gcd hdvd (pow_dvd_pow p (by omega))
    obtain ⟨j, _, hjeq⟩ :=
      (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right m (p ^ e))
    have hjm : p ^ j ∣ m := hjeq ▸ Nat.gcd_dvd_left m (p ^ e)
    have hjlt : j ≤ e - 1 := by
      by_contra hc
      exact hndvd (dvd_trans (pow_dvd_pow p (by omega)) hjm)
    have hpj : p ^ (e - 1) ∣ p ^ j := hjeq ▸ hle
    have hje : e - 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hpj
    rw [hjeq]
    congr 1
    omega
  have h2 : p ^ (e - 1) * Nat.lcm m (p ^ e) = p ^ (e - 1) * (m * p) := by
    calc p ^ (e - 1) * Nat.lcm m (p ^ e)
        = Nat.gcd m (p ^ e) * Nat.lcm m (p ^ e) := by rw [hgcd]
      _ = m * p ^ e := Nat.gcd_mul_lcm m (p ^ e)
      _ = m * (p ^ (e - 1) * p) := by
          rw [← pow_succ]
          congr 2
          omega
      _ = p ^ (e - 1) * (m * p) := by ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h2

/-- R2.3: the order of the simple factor is the prime of the prime-power rank. -/
theorem simpleFactorOrder_eq {J : Current} {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hrank : J.rank = p ^ e) : simpleFactorOrder J = p := by
  obtain ⟨hdvd, hndvd⟩ := primePow_valuation J hp he hrank
  have hmpos : 0 < Nat.card (Flt J) := card_Flt_pos J
  have hcard := card_simpleFactor_mul J
  rw [card_F_eq J, hrank, lcm_of_valuation hp he hdvd hndvd] at hcard
  exact Nat.eq_of_mul_eq_mul_right hmpos (by rw [hcard]; ring)

/-- R2.3: the simple factor of a current has prime order. -/
theorem simpleFactor_card_prime (J : Current) : Nat.Prime (simpleFactorOrder J) := by
  obtain ⟨p, e, hp, he, hrank⟩ := J.exists_primePow
  rw [simpleFactorOrder_eq hp he hrank]
  exact hp

/-- R2.3: every element of the simple factor is annihilated by the order of
that simple factor.  This is the canonical `p_J`-torsion structure carried by
`S_J` itself. -/
theorem simpleFactor_nsmul_eq_zero (J : Current) (x : SimpleFactor J) :
    simpleFactorOrder J • x = 0 :=
  card_nsmul_eq_zero'

/-- R2.3: the canonical `F_{p_J}`-scalar structure on the simple factor,
obtained from its own `p_J`-torsion additive-group structure.  No basis and no
choice of additive equivalence enters this construction. -/
noncomputable instance simpleFactorModule (J : Current) :
    Module (ZMod (simpleFactorOrder J)) (SimpleFactor J) :=
  AddCommGroup.zmodModule (simpleFactor_nsmul_eq_zero J)

/-- The canonical scalar action restricts along `ℕ → ZMod p_J` to the ambient
additive-group action, which is what makes it the intrinsic one. -/
theorem simpleFactor_natCast_smul (J : Current) (c : ℕ) (x : SimpleFactor J) :
    ((c : ZMod (simpleFactorOrder J)) • x) = c • x :=
  Nat.cast_smul_eq_nsmul _ c x

/-- The class in `S_J` of a vertex of `J` outside the lower-current stage is
nonzero.  This is the intrinsic source of a frame for `S_J`. -/
private theorem exists_ne_zero_simpleFactor (J : Current) :
    ∃ x : SimpleFactor J, x ≠ 0 := by
  obtain ⟨y, hyJ, hyF⟩ : ∃ y, y ∈ J.toSubgroup ∧ y ∉ Flt J := by
    by_contra hc
    refine not_le_Flt J fun y hy ↦ ?_
    by_contra hyF
    exact hc ⟨y, hy, hyF⟩
  have hyFJ : y ∈ F J := (le_sup_right : J.toSubgroup ≤ F J) hyJ
  refine ⟨QuotientAddGroup.mk (⟨y, hyFJ⟩ : F J), ?_⟩
  rw [Ne, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  exact hyF

/-- R2.3: the simple factor of a current is a one-dimensional vector object
over the prime field `F_{p_J}` of its own order.  The scalar structure is the
canonical torsion one; only the frame is asserted to exist. -/
theorem simpleFactor_oneDimensional (J : Current) :
    Nonempty (ZMod (simpleFactorOrder J) ≃ₗ[ZMod (simpleFactorOrder J)]
      SimpleFactor J) := by
  haveI hp : Fact (Nat.Prime (simpleFactorOrder J)) := ⟨simpleFactor_card_prime J⟩
  haveI : NeZero (simpleFactorOrder J) := ⟨hp.out.ne_zero⟩
  haveI : Finite (SimpleFactor J) := Nat.finite_of_card_ne_zero hp.out.ne_zero
  obtain ⟨x, hx⟩ := exists_ne_zero_simpleFactor J
  let f : ZMod (simpleFactorOrder J) →ₗ[ZMod (simpleFactorOrder J)] SimpleFactor J :=
    { toFun := fun c ↦ c • x
      map_add' := fun a b ↦ add_smul a b x
      map_smul' := fun a b ↦ by simpa using mul_smul a b x }
  have hker : ∀ c : ZMod (simpleFactorOrder J), c • x = 0 → c = 0 := by
    intro c hc
    by_contra hcne
    apply hx
    calc x = (1 : ZMod (simpleFactorOrder J)) • x := (one_smul _ _).symm
      _ = (c⁻¹ * c) • x := by rw [inv_mul_cancel₀ hcne]
      _ = c⁻¹ • c • x := mul_smul _ _ _
      _ = 0 := by rw [hc, smul_zero]
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : a • x = b • x := hab
    have hsub : (a - b) • x = 0 := by rw [sub_smul, hab', sub_self]
    exact sub_eq_zero.1 (hker _ hsub)
  have hcard : Nat.card (ZMod (simpleFactorOrder J)) = Nat.card (SimpleFactor J) := by
    rw [Nat.card_zmod, simpleFactorOrder]
  exact ⟨LinearEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)⟩

/-- The underlying cyclic-group form of R2.3, obtained by forgetting the
canonical scalar structure of the one-dimensional statement. -/
theorem simpleFactor_addEquiv_zmod (J : Current) :
    Nonempty (ZMod (simpleFactorOrder J) ≃+ SimpleFactor J) := by
  obtain ⟨e⟩ := simpleFactor_oneDimensional J
  exact ⟨e.toAddEquiv⟩

/-! ## R2.6 — intrinsic height -/

/-- The intrinsic height of a current: the number of currents below it. -/
noncomputable def Current.height (J : Current) : ℕ := Nat.card {R : Current // R ≤ J}

private noncomputable def heightEquiv {J : Current} {p e : ℕ} (hp : p.Prime)
    (hrank : J.rank = p ^ e) : Fin e ≃ {R : Current // R ≤ J} := by
  refine Equiv.ofBijective
    (fun i ↦ ⟨currentOfPrimePow (p ^ (i.1 + 1))
      (isPrimePow_pow hp (Nat.succ_pos _)), ?_⟩) ?_
  · rw [Current.le_iff_rank_dvd, rank_currentOfPrimePow, hrank]
    exact pow_dvd_pow p (by omega)
  constructor
  · intro i j hij
    have hr : p ^ (i.1 + 1) = p ^ (j.1 + 1) := by
      have h := congrArg (fun R : {R : Current // R ≤ J} ↦ R.1.rank) hij
      simpa using h
    have := Nat.pow_right_injective hp.two_le hr
    exact Fin.ext (by omega)
  · rintro ⟨R, hR⟩
    obtain ⟨q, f, hq, hf, hqf⟩ := R.exists_primePow
    have hdvd : R.rank ∣ J.rank := (Current.le_iff_rank_dvd R J).1 hR
    rw [hrank, hqf] at hdvd
    have hqp : q = p := by
      have h1 : q ∣ p ^ e := dvd_trans (dvd_pow_self q hf.ne') hdvd
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1)
    subst hqp
    have hfe : f ≤ e := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).1 hdvd
    refine ⟨⟨f - 1, by omega⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply ext_index
    have hval : (currentOfPrimePow (q ^ (f - 1 + 1))
        (isPrimePow_pow hp (Nat.succ_pos (f - 1)))).rank = R.rank := by
      rw [rank_currentOfPrimePow, hqf]
      congr 1
      omega
    exact hval

theorem Current.height_eq {J : Current} {p e : ℕ} (hp : p.Prime)
    (hrank : J.rank = p ^ e) : J.height = e := by
  rw [height, ← Nat.card_congr (heightEquiv hp hrank), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- R2.6: the rank of a current is the prime of its simple factor raised to its
intrinsic height. -/
theorem current_rank_eq_primePow_height (J : Current) :
    J.rank = simpleFactorOrder J ^ J.height := by
  obtain ⟨p, e, hp, he, hrank⟩ := J.exists_primePow
  rw [simpleFactorOrder_eq hp he hrank, Current.height_eq hp hrank, hrank]

theorem Current.height_pos (J : Current) : 0 < J.height := by
  obtain ⟨p, e, hp, he, hrank⟩ := J.exists_primePow
  rw [Current.height_eq hp hrank]
  exact he

/-! ## Higher currents and the predecessor map -/

/-- The higher currents: those of intrinsic height at least two. -/
def HigherCurrent := {J : Current // 2 ≤ J.height}

private theorem higherCurrent_data (J : HigherCurrent) :
    ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ J.1.rank = p ^ e ∧ simpleFactorOrder J.1 = p := by
  obtain ⟨p, e, hp, he, hrank⟩ := J.1.exists_primePow
  have hh : J.1.height = e := Current.height_eq hp hrank
  exact ⟨p, e, hp, hh ▸ J.2, hrank, simpleFactorOrder_eq hp he hrank⟩

/-- The predecessor of a higher current: the current one step lower in its own
prime-power chain. -/
noncomputable def predecessor (J : HigherCurrent) : Current :=
  currentOfPrimePow (J.1.rank / simpleFactorOrder J.1) (by
    obtain ⟨p, e, hp, he2, hrank, hord⟩ := higherCurrent_data J
    rw [hord, hrank, pow_div_self hp.pos (by omega)]
    exact isPrimePow_pow hp (by omega))

private theorem rank_predecessor (J : HigherCurrent) {p e : ℕ} (hp : p.Prime)
    (he2 : 2 ≤ e) (hrank : J.1.rank = p ^ e) (hord : simpleFactorOrder J.1 = p) :
    (predecessor J).rank = p ^ (e - 1) := by
  rw [predecessor, rank_currentOfPrimePow, hord, hrank,
    pow_div_self hp.pos (by omega)]

/-- R2.6: the predecessor of a higher current has rank one prime factor
smaller. -/
theorem predecessor_spec (J : HigherCurrent) :
    (predecessor J).rank * simpleFactorOrder J.1 = J.1.rank := by
  obtain ⟨p, e, hp, he2, hrank, hord⟩ := higherCurrent_data J
  rw [rank_predecessor J hp he2 hrank hord, hord, hrank, ← pow_succ]
  congr 1
  omega

theorem predecessor_height (J : HigherCurrent) :
    (predecessor J).height + 1 = J.1.height := by
  obtain ⟨p, e, hp, he2, hrank, hord⟩ := higherCurrent_data J
  rw [Current.height_eq hp (rank_predecessor J hp he2 hrank hord),
    Current.height_eq hp hrank]
  omega

/-! ## R2.4, R2.5 — canonical endpoints -/

/-- The canonical endpoint `F_X`: the join of all currents of rank at most
`X`. -/
noncomputable def endpointSubgroup (X : ℕ) : AddSubgroup CenteredResidueGroup :=
  ⨆ J : Current, ⨆ _ : J.rank ≤ X, J.toSubgroup

theorem endpointSubgroup_le_H_factorial (X : ℕ) :
    endpointSubgroup X ≤ compactSubgroupH (Nat.factorial X) := by
  refine iSup_le fun R ↦ iSup_le fun hR ↦ ?_
  rw [R.toSubgroup_eq]
  exact compactSubgroupH_mono (Nat.dvd_factorial R.rank_pos hR)

/-- R2.4: every canonical endpoint is compact. -/
theorem endpoint_finite (X : ℕ) : IsCompactElement (endpointSubgroup X) :=
  isCompactElement_of_le_H (Nat.factorial_pos X) (endpointSubgroup_le_H_factorial X)

/-- The canonical endpoint as a compact stage. -/
noncomputable def endpoint (X : ℕ) : CompactSubgroupStage :=
  ⟨endpointSubgroup X, endpoint_finite X⟩

theorem endpointSubgroup_mono : Monotone endpointSubgroup := by
  intro X Y hXY
  refine iSup_le fun R ↦ iSup_le fun hR ↦ ?_
  exact le_iSup_of_le R (le_iSup_of_le (hR.trans hXY) le_rfl)

theorem endpoint_mono : Monotone endpoint := fun _ _ h ↦ endpointSubgroup_mono h

/-- A current lies below an endpoint exactly when its rank is within the
endpoint bound. -/
theorem endpoint_current_iff (J : Current) (X : ℕ) :
    J.toSubgroup ≤ endpointSubgroup X ↔ J.rank ≤ X := by
  constructor
  · intro h
    obtain ⟨R, hR, hdvd⟩ :=
      exists_current_of_le_iSup (P := fun R : Current ↦ R.rank ≤ X) J.exists_primePow h
    exact (Nat.le_of_dvd R.rank_pos hdvd).trans hR
  · intro h
    exact le_iSup_of_le J (le_iSup_of_le h le_rfl)

/-- R2.5: every compact stage lies below the endpoint of any bound dominating
all of its prime-power divisors. -/
theorem compactSubgroupH_le_endpoint :
    ∀ n : ℕ, 0 < n → ∀ X : ℕ, (∀ q : ℕ, IsPrimePow q → q ∣ n → q ≤ X) →
      compactSubgroupH n ≤ endpointSubgroup X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn X hX
    rcases Nat.lt_or_ge n 2 with h1 | h1
    · have hn1 : n = 1 := by omega
      rw [hn1, compactSubgroupH_one]
      exact bot_le
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      obtain ⟨k, m, hm, hnkm⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, pow_zero, one_mul] at hnkm
          exact absurd (hnkm ▸ hpn) hm
        · exact hk0
      have hapos : 0 < p ^ k := pow_pos hp.pos k
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · rw [hm0, mul_zero] at hnkm
          omega
        · exact hm0
      have hcop : Nat.Coprime (p ^ k) m :=
        Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
      have hpa : IsPrimePow (p ^ k) := isPrimePow_pow hp hk
      have halt : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
      have hblt : m < n := by
        calc m = 1 * m := (one_mul m).symm
          _ < p ^ k * m := Nat.mul_lt_mul_of_lt_of_le halt le_rfl hmpos
          _ = n := hnkm.symm
      have hAle : compactSubgroupH (p ^ k) ≤ endpointSubgroup X := by
        have hrk := (endpoint_current_iff (currentOfPrimePow (p ^ k) hpa) X).2
          (by rw [rank_currentOfPrimePow]; exact hX (p ^ k) hpa ⟨m, hnkm⟩)
        rwa [(currentOfPrimePow (p ^ k) hpa).toSubgroup_eq,
          rank_currentOfPrimePow] at hrk
      have hBle : compactSubgroupH m ≤ endpointSubgroup X :=
        ih m hblt hmpos X fun q hq hqm ↦
          hX q hq (hqm.trans ⟨p ^ k, by rw [hnkm]; ring⟩)
      have hlcm : Nat.lcm (p ^ k) m = n := by
        rw [Nat.Coprime.lcm_eq_mul hcop, ← hnkm]
      rw [← hlcm, ← compactSubgroupH_sup hapos hmpos]
      exact sup_le hAle hBle

/-- R2.5: the canonical endpoints are cofinal among the compact stages. -/
theorem endpoint_cofinal (K : CompactSubgroupStage) : ∃ X : ℕ, K ≤ endpoint X := by
  refine ⟨K.index, ?_⟩
  show K.1 ≤ endpointSubgroup K.index
  rw [K.coe_eq]
  exact compactSubgroupH_le_endpoint K.index K.index_pos K.index
    fun q _ hq ↦ Nat.le_of_dvd K.index_pos hq

/-- The endpoint system: the image of the canonical endpoint map, ordered by
inclusion. -/
def Endpoint : Set CompactSubgroupStage := Set.range endpoint

end Erdos289
