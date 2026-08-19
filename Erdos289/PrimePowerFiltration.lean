module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection.Centering
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Erdos289.PathSupport
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

/-!
# Canonical prime-power filtration of the target residue group

For `A = ℚ/ℤ`, the stage `J_q` is intrinsically the kernel of multiplication
by `q`.  Before a prime power `Q`, the lower stage is the join of all `J_R`
for earlier prime powers; the current stage adjoins `J_Q`.  The simple fibre is
the resulting subquotient.  No lcm coordinate or basis of the fibre is chosen.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The target-centered residue group `ℚ/ℤ`. -/
abbrev TargetResidue := AffineCorrection.CenteredValue ℚ 1

/-- Canonical centered observation of one reciprocal denominator. -/
def reciprocalResidue (n : Denominator) : TargetResidue :=
  AffineCorrection.CenteredValue.mk (1 : ℚ) (reciprocal n)

/-- Canonical centered observation of a finite reciprocal support. -/
def Support.residue (S : Support) : TargetResidue :=
  AffineCorrection.CenteredValue.mk (1 : ℚ) S.value

/-- `J_q = ker([q] : ℚ/ℤ → ℚ/ℤ)`. -/
def annihilatorStage (q : ℕ) : AddSubgroup TargetResidue :=
  (nsmulAddMonoidHom (α := TargetResidue) q).ker

/-- A reciprocal point lies in the annihilator stage indexed by its denominator. -/
theorem reciprocalResidue_mem_annihilatorStage (n : Denominator) :
    reciprocalResidue n ∈ annihilatorStage n.1 := by
  change n.1 • reciprocalResidue n = 0
  unfold reciprocalResidue
  rw [← map_nsmul]
  change AffineCorrection.CenteredValue.mk (1 : ℚ)
      (n.1 • reciprocal n) = 0
  have hn0 : (n.1 : ℚ) ≠ 0 := by exact_mod_cast n.2.ne'
  rw [nsmul_eq_mul]
  simp [reciprocal, hn0]

/-- The exact additive order criterion for a reciprocal residue. -/
theorem nsmul_reciprocalResidue_eq_zero_iff (m : ℕ) (n : Denominator) :
    m • reciprocalResidue n = 0 ↔ n.1 ∣ m := by
  unfold reciprocalResidue
  rw [← map_nsmul]
  change ((↑(m • reciprocal n) : TargetResidue) = 0) ↔ n.1 ∣ m
  rw [QuotientAddGroup.eq_zero_iff (m • reciprocal n)]
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨z, hz⟩
    have hrat : (z : ℚ) = (m : ℚ) / n.1 := by
      simpa [reciprocal, nsmul_eq_mul, div_eq_mul_inv] using hz
    have hn0 : (n.1 : ℚ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hmulQ : (z : ℚ) * n.1 = m := (eq_div_iff hn0).mp hrat
    have hmulZ : z * (n.1 : ℤ) = m := by exact_mod_cast hmulQ
    apply Int.natCast_dvd_natCast.mp
    exact ⟨z, by simpa [mul_comm] using hmulZ.symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨(k : ℤ), ?_⟩
    have hn0 : (n.1 : ℚ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hcalc : (k : ℚ) = ((n.1 * k : ℕ) : ℚ) * (n.1 : ℚ)⁻¹ := by
      rw [Nat.cast_mul]
      calc
        (k : ℚ) = (k : ℚ) * ((n.1 : ℚ) * (n.1 : ℚ)⁻¹) := by simp [hn0]
        _ = ((n.1 : ℚ) * k) * (n.1 : ℚ)⁻¹ := by
          simp [mul_assoc, mul_comm]
    simpa [reciprocal, nsmul_eq_mul, div_eq_mul_inv] using hcalc

/-- The centered observation of a disjoint union is additive. -/
theorem Support.residue_union {S T : Support} (h : Disjoint S T) :
    (S ∪ T).residue = S.residue + T.residue := by
  unfold Support.residue
  rw [Support.value_union h, map_add]

/-- Centered support observation is the additive fold of reciprocal residues. -/
theorem Support.residue_eq_sum (S : Support) :
    S.residue = ∑ n ∈ S, reciprocalResidue n := by
  unfold Support.residue Support.value reciprocalResidue
  rw [map_sum]

/-- Join of the annihilator stages indexed by prime powers strictly below `Q`. -/
def lowerPrimePowerStage (Q : ℕ) : AddSubgroup TargetResidue :=
  ⨆ (R : ℕ) (_ : R < Q) (_ : IsPrimePow R), annihilatorStage R

/-- The lower stage with the current annihilator stage adjoined. -/
def primePowerStage (Q : ℕ) : AddSubgroup TargetResidue :=
  lowerPrimePowerStage Q ⊔ annihilatorStage Q

/-- The lower stage regarded as a subgroup of the current stage. -/
def lowerInsidePrimePowerStage (Q : ℕ) : AddSubgroup (primePowerStage Q) :=
  (lowerPrimePowerStage Q).comap (primePowerStage Q).subtype

/-- The associated simple fibre `F_Q / F_{<Q}`. -/
abbrev PrimePowerSimpleFibre (Q : ℕ) :=
  (primePowerStage Q) ⧸ lowerInsidePrimePowerStage Q

theorem lowerPrimePowerStage_le (Q : ℕ) :
    lowerPrimePowerStage Q ≤ primePowerStage Q :=
  le_sup_left

theorem annihilatorStage_le (Q : ℕ) :
    annihilatorStage Q ≤ primePowerStage Q :=
  le_sup_right

/-- The annihilator-stage functor is monotone for divisibility. -/
theorem annihilatorStage_mono_dvd {q r : ℕ} (hqr : q ∣ r) :
    annihilatorStage q ≤ annihilatorStage r := by
  rintro x hx
  change r • x = 0
  rcases hqr with ⟨k, rfl⟩
  change q • x = 0 at hx
  calc
    (q * k) • x = k • (q • x) := mul_nsmul x q k
    _ = 0 := by rw [hx, nsmul_zero]

private theorem nsmul_zsmul_nsmul
    {G : Type*} [AddCommGroup G] (m n : ℕ) (a : ℤ) (x : G) :
    m • (a • (n • x)) = a • ((m * n) • x) := by
  simp only [← natCast_zsmul, smul_smul]
  congr 1
  simp [Nat.cast_mul, mul_left_comm]

/-- Coprime annihilator stages compose by their canonical join. -/
theorem annihilatorStage_mul_eq_sup_of_coprime
    {m n : ℕ} (hcop : m.Coprime n) :
    annihilatorStage (m * n) = annihilatorStage m ⊔ annihilatorStage n := by
  apply le_antisymm
  · intro x hx
    change (m * n) • x = 0 at hx
    let a : ℤ := m.gcdA n
    let b : ℤ := m.gcdB n
    have hbez : (m : ℤ) * a + (n : ℤ) * b = 1 := by
      simpa [a, b, hcop.gcd_eq_one] using (Nat.gcd_eq_gcd_ab m n).symm
    let y : TargetResidue := b • (n • x)
    let z : TargetResidue := a • (m • x)
    rw [AddSubgroup.mem_sup]
    refine ⟨y, ?_, z, ?_, ?_⟩
    · change m • y = 0
      rw [show m • y = b • ((m * n) • x) by
        exact nsmul_zsmul_nsmul m n b x]
      rw [hx, zsmul_zero]
    · change n • z = 0
      rw [show n • z = a • ((n * m) • x) by
        exact nsmul_zsmul_nsmul n m a x]
      rw [Nat.mul_comm n m, hx, zsmul_zero]
    · dsimp [y, z]
      calc
        b • (n • x) + a • (m • x) =
            ((n : ℤ) * b + (m : ℤ) * a) • x := by
              simp only [← natCast_zsmul, smul_smul, add_zsmul]
              simp [mul_comm]
        _ = x := by rw [add_comm, hbez, one_zsmul]
  · apply sup_le
    · exact annihilatorStage_mono_dvd (dvd_mul_right m n)
    · exact annihilatorStage_mono_dvd (dvd_mul_left n m)

/-- A product of pairwise-coprime annihilator stages is controlled componentwise. -/
theorem annihilatorStage_prod_le
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℕ)
    (H : AddSubgroup TargetResidue)
    (hpair : (s : Set I).Pairwise fun i j ↦ (f i).Coprime (f j))
    (hle : ∀ i ∈ s, annihilatorStage (f i) ≤ H) :
    annihilatorStage (∏ i ∈ s, f i) ≤ H := by
  induction s using Finset.induction_on with
  | empty =>
      intro x hx
      change (1 : ℕ) • x = 0 at hx
      have hx0 : x = 0 := by simpa using hx
      exact hx0 ▸ H.zero_mem
  | @insert a s has ih =>
      have hpairS : (s : Set I).Pairwise fun i j ↦ (f i).Coprime (f j) :=
        hpair.mono (by intro i hi; simp [hi])
      have hacop : (f a).Coprime (∏ i ∈ s, f i) := by
        rw [Nat.coprime_prod_right_iff]
        intro i hi
        exact hpair (by simp) (by simp [hi]) (by
          intro hai
          subst i
          exact has hi)
      rw [Finset.prod_insert has, annihilatorStage_mul_eq_sup_of_coprime hacop]
      exact sup_le (hle a (by simp))
        (ih hpairS (by intro i hi; exact hle i (by simp [hi])))

/-- Every bounded denominator observation is already in the bounded prime-power join. -/
theorem annihilatorStage_le_lower_of_lt
    {n Q : ℕ} (hn : 0 < n) (hnQ : n < Q) :
    annihilatorStage n ≤ lowerPrimePowerStage Q := by
  let P := n.primeFactors
  let f : P → ℕ := fun p ↦ (p : ℕ) ^ n.factorization p
  have hprod : n = ∏ p : P, f p := by
    simpa [P, f] using Nat.prod_primeFactors_coe_pow_factorization hn.ne'
  rw [hprod]
  apply annihilatorStage_prod_le Finset.univ f (lowerPrimePowerStage Q)
  · intro p _hp q _hq hpq
    exact Nat.pairwise_coprime_pow_primeFactors_factorization hpq
  · intro p _hp
    have hpprime : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have he : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact p.2
    have hfpp : IsPrimePow (f p) :=
      ⟨p, n.factorization p, hpprime.prime, Nat.pos_iff_ne_zero.2 he, rfl⟩
    have hfdvdprod : f p ∣ ∏ q : P, f q :=
      Finset.dvd_prod_of_mem f (Finset.mem_univ p)
    have hfdvdn : f p ∣ n := by simpa [hprod] using hfdvdprod
    have hfpos : 0 < f p := pow_pos hpprime.pos _
    have hflt : f p < Q := lt_of_le_of_lt (Nat.le_of_dvd hn hfdvdn) hnQ
    unfold lowerPrimePowerStage
    exact le_iSup_of_le (f p) <| le_iSup_of_le hflt <|
      le_iSup_of_le hfpp le_rfl

/-- A coprime product of two bounded denominator stages lies in the lower join. -/
theorem annihilatorStage_mul_le_lower_of_coprime_lt
    {a b Q : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haQ : a < Q) (hbQ : b < Q) (hab : a.Coprime b) :
    annihilatorStage (a * b) ≤ lowerPrimePowerStage Q := by
  rw [annihilatorStage_mul_eq_sup_of_coprime hab]
  exact sup_le (annihilatorStage_le_lower_of_lt ha haQ)
    (annihilatorStage_le_lower_of_lt hb hbQ)

/-- The reciprocal of a coprime product of bounded factors is lower-supported. -/
theorem reciprocalResidue_mul_mem_lower_of_coprime_lt
    {a b Q : ℕ} (ha : 0 < a) (hb : 0 < b)
    (haQ : a < Q) (hbQ : b < Q) (hab : a.Coprime b) :
    reciprocalResidue ⟨a * b, Nat.mul_pos ha hb⟩ ∈ lowerPrimePowerStage Q :=
  annihilatorStage_mul_le_lower_of_coprime_lt ha hb haQ hbQ hab
    (reciprocalResidue_mem_annihilatorStage ⟨a * b, Nat.mul_pos ha hb⟩)

/-- The `q`-torsion of `ℚ/ℤ` is the cyclic group generated by `1/q`. -/
theorem annihilatorStage_eq_zmultiples {q : ℕ} (hq : 0 < q) :
    annihilatorStage q = AddSubgroup.zmultiples (reciprocalResidue ⟨q, hq⟩) := by
  refine le_antisymm ?_ (AddSubgroup.zmultiples_le.2
    (reciprocalResidue_mem_annihilatorStage ⟨q, hq⟩))
  rintro x hx
  obtain ⟨r, rfl⟩ :=
    QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℚ)) x
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hx' : q • (QuotientAddGroup.mk r : TargetResidue) = 0 := hx
  have h0 : ((q • r : ℚ) : TargetResidue) = 0 := hx'
  obtain ⟨k, hk⟩ :=
    AddSubgroup.mem_zmultiples_iff.1 ((QuotientAddGroup.eq_zero_iff _).1 h0)
  have hqr : (q : ℚ) * r = (k : ℚ) := by
    simpa [nsmul_eq_mul, zsmul_eq_mul] using hk.symm
  have hr : r = (k : ℚ) / q := by
    rw [eq_div_iff hq0, mul_comm]
    exact hqr
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  show (k : ℤ) • AffineCorrection.CenteredValue.mk (1 : ℚ) (reciprocal ⟨q, hq⟩)
      = QuotientAddGroup.mk r
  have hval : (k : ℤ) • reciprocal ⟨q, hq⟩ = r := by
    rw [hr, zsmul_eq_mul]
    unfold reciprocal
    rw [mul_one_div]
  rw [← map_zsmul, hval]
  rfl

/-- The lower stage of a current is annihilated by any common multiple of the
prime powers below it. -/
theorem lowerPrimePowerStage_le_annihilatorStage {Q D : ℕ}
    (h : ∀ R : ℕ, R < Q → IsPrimePow R → R ∣ D) :
    lowerPrimePowerStage Q ≤ annihilatorStage D :=
  iSup_le fun R => iSup_le fun hR => iSup_le fun hRpp =>
    annihilatorStage_mono_dvd (h R hR hRpp)

/-- The core's cyclic subgroup sits inside the lower stage of any later
current: the first endpoint condition of the tail chain. -/
theorem zmultiples_reciprocalResidue_le_lowerPrimePowerStage
    {D Q : ℕ} (hD : 0 < D) (hDQ : D < Q) :
    AddSubgroup.zmultiples (reciprocalResidue ⟨D, hD⟩) ≤ lowerPrimePowerStage Q :=
  AddSubgroup.zmultiples_le.2
    (annihilatorStage_le_lower_of_lt hD hDQ
      (reciprocalResidue_mem_annihilatorStage ⟨D, hD⟩))

/-- A current factor times a coprime bounded factor has its whole annihilator
stage supported at the current prime-power stage. -/
theorem annihilatorStage_mul_le_primePowerStage
    {Q k : ℕ} (hk : 0 < k) (hkQ : k < Q) (hcop : Q.Coprime k) :
    annihilatorStage (Q * k) ≤ primePowerStage Q := by
  rw [annihilatorStage_mul_eq_sup_of_coprime hcop]
  exact sup_le (annihilatorStage_le Q)
    (le_trans (annihilatorStage_le_lower_of_lt hk hkQ)
      (lowerPrimePowerStage_le Q))

/-- The core exponent of a current: the least common multiple of all
denominators below it.  Its torsion subgroup contains the whole lower stage,
which is what makes it the right modulus for the core torsor sitting under the
tail chain that starts at this current. -/
def coreExponent (Q : ℕ) : ℕ :=
  (Finset.Icc 1 (Q - 1)).lcm id

theorem coreExponent_ne_zero (Q : ℕ) : coreExponent Q ≠ 0 := by
  simp [coreExponent, Finset.lcm_eq_zero_iff]

theorem coreExponent_pos (Q : ℕ) : 0 < coreExponent Q :=
  Nat.pos_of_ne_zero (coreExponent_ne_zero Q)

private abbrev lowerStageExponent (Q : ℕ) : ℕ := coreExponent Q

private theorem lowerStageExponent_ne_zero (Q : ℕ) :
    lowerStageExponent Q ≠ 0 := coreExponent_ne_zero Q

/-- The lower stage of a current is annihilated by its core exponent. -/
theorem lowerPrimePowerStage_le_annihilatorStage_coreExponent (Q : ℕ) :
    lowerPrimePowerStage Q ≤ annihilatorStage (coreExponent Q) := by
  unfold lowerPrimePowerStage
  refine iSup_le fun R => iSup_le fun hRQ => iSup_le fun hRpp => ?_
  apply annihilatorStage_mono_dvd
  apply Finset.dvd_lcm
  exact Finset.mem_Icc.mpr ⟨hRpp.pos, Nat.le_sub_one_of_lt hRQ⟩

/--
The bottom endpoint of the tail chain: the lower stage of a current is
contained in the cyclic group generated by the reciprocal of its core
exponent.  Taking that as the core subgroup makes the chain start exactly
where the core torsor ends.
-/
theorem lowerPrimePowerStage_le_zmultiples_coreExponent (Q : ℕ) :
    lowerPrimePowerStage Q ≤
      AddSubgroup.zmultiples
        (reciprocalResidue ⟨coreExponent Q, coreExponent_pos Q⟩) := by
  rw [← annihilatorStage_eq_zmultiples (coreExponent_pos Q)]
  exact lowerPrimePowerStage_le_annihilatorStage_coreExponent Q

private theorem lowerPrimePowerStage_le_annihilatorStage_lowerStageExponent
    (Q : ℕ) :
    lowerPrimePowerStage Q ≤ annihilatorStage (lowerStageExponent Q) :=
  lowerPrimePowerStage_le_annihilatorStage_coreExponent Q

private theorem prime_pow_not_dvd_lowerStageExponent
    {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ¬p ^ e ∣ lowerStageExponent (p ^ e) := by
  intro hdvd
  have hfacLe : e ≤ (lowerStageExponent (p ^ e)).factorization p :=
    (hp.pow_dvd_iff_le_factorization
      (lowerStageExponent_ne_zero (p ^ e))).mp hdvd
  have hfacLt : (lowerStageExponent (p ^ e)).factorization p < e := by
    rw [lowerStageExponent, coreExponent, Finset.factorization_lcm]
    · apply (Finset.sup_lt_iff he).2
      intro m hm
      have hmBounds := Finset.mem_Icc.mp hm
      by_contra hnot
      have hpowdvd : p ^ e ∣ m :=
        (hp.pow_dvd_iff_le_factorization (by omega)).2
          (Nat.le_of_not_gt hnot)
      have hpowle : p ^ e ≤ m := Nat.le_of_dvd hmBounds.1 hpowdvd
      omega
    · intro m hm
      have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
      simpa using hmpos.ne'
  exact (Nat.not_le_of_lt hfacLt) hfacLe

/--
The lower stage has a common annihilator that misses the current prime power.
This is the only consequence of the `lcm` coordinate that leaves this module.
-/
theorem exists_lowerAnnihilator {Q p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) :
    ∃ L : ℕ, 0 < L ∧ (∀ x ∈ lowerPrimePowerStage Q, L • x = 0) ∧ ¬p ^ e ∣ L := by
  refine ⟨lowerStageExponent Q, Nat.pos_of_ne_zero (lowerStageExponent_ne_zero Q),
    fun x hx => lowerPrimePowerStage_le_annihilatorStage_lowerStageExponent Q hx, ?_⟩
  subst hQ
  exact prime_pow_not_dvd_lowerStageExponent hp he

/-- A reciprocal whose denominator contains the current prime power has
nonzero image above the lower stage. -/
theorem reciprocalResidue_primePow_mul_not_mem_lower
    {Q p e k : ℕ} (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (hQpos : 0 < Q) (hk : 0 < k) :
    reciprocalResidue ⟨Q * k, Nat.mul_pos hQpos hk⟩ ∉
      lowerPrimePowerStage Q := by
  intro hmem
  have hkill : lowerStageExponent Q •
      reciprocalResidue ⟨Q * k, Nat.mul_pos hQpos hk⟩ = 0 :=
    lowerPrimePowerStage_le_annihilatorStage_lowerStageExponent Q hmem
  have hQkdvd : Q * k ∣ lowerStageExponent Q :=
    (nsmul_reciprocalResidue_eq_zero_iff _ _).mp hkill
  have hQdvd : Q ∣ lowerStageExponent Q :=
    (dvd_mul_right Q k).trans hQkdvd
  subst Q
  exact prime_pow_not_dvd_lowerStageExponent hp he hQdvd

/-- The canonical lower filtration is monotone in the prime-power order. -/
theorem lowerPrimePowerStage_mono {Q Q' : ℕ} (h : Q ≤ Q') :
    lowerPrimePowerStage Q ≤ lowerPrimePowerStage Q' := by
  unfold lowerPrimePowerStage
  refine iSup_le fun R => iSup_le fun hRQ => iSup_le fun hpp => ?_
  exact le_iSup_of_le R <| le_iSup_of_le (lt_of_lt_of_le hRQ h) <|
    le_iSup_of_le hpp le_rfl

/-- Every reciprocal at an earlier prime-power denominator lies in the lower stage. -/
theorem reciprocalResidue_mem_lower_of_primePow_lt
    {R Q : ℕ} (hRpos : 0 < R) (hRQ : R < Q) (hRpp : IsPrimePow R) :
    reciprocalResidue ⟨R, hRpos⟩ ∈ lowerPrimePowerStage Q := by
  have hle : annihilatorStage R ≤ lowerPrimePowerStage Q := by
    unfold lowerPrimePowerStage
    exact le_iSup_of_le R <| le_iSup_of_le hRQ <|
      le_iSup_of_le hRpp le_rfl
  exact hle (reciprocalResidue_mem_annihilatorStage ⟨R, hRpos⟩)

/-- Every earlier prime-power stage is already contained in a later lower stage. -/
theorem primePowerStage_le_lower_of_lt
    {Q Q' : ℕ} (hQ : IsPrimePow Q) (h : Q < Q') :
    primePowerStage Q ≤ lowerPrimePowerStage Q' := by
  apply sup_le
  · exact lowerPrimePowerStage_mono h.le
  · unfold lowerPrimePowerStage
    exact le_iSup_of_le Q <| le_iSup_of_le h <| le_iSup_of_le hQ le_rfl

end Erdos289
