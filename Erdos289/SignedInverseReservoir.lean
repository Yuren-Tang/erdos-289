module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.SignedInverseAtom
public import Erdos289.PrimeSupply
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

/-!
# Realization of intrinsic transverse reservoirs

This internal arithmetic module forgets a finite family of signed-inverse
witnesses into the canonical `TransverseReservoir` and
`CompatibleTransversePool` interfaces.  The candidate coordinates do not
cross the provider boundary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

private theorem primeFinset_prod_dvd
    (A : Finset ℕ) (N : ℕ)
    (hprime : ∀ q ∈ A, q.Prime) (hdvd : ∀ q ∈ A, q ∣ N) :
    (∏ q ∈ A, q) ∣ N := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert q A hq ih =>
      rw [Finset.prod_insert hq]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · apply Nat.Coprime.prod_right
        intro r hr
        exact (Nat.coprime_primes
          (hprime q (Finset.mem_insert_self q A))
          (hprime r (Finset.mem_insert_of_mem hr))).2 (by
            intro hqr
            exact hq (hqr ▸ hr))
      · exact hdvd q (Finset.mem_insert_self q A)
      · exact ih
          (fun r hr ↦ hprime r (Finset.mem_insert_of_mem hr))
          (fun r hr ↦ hdvd r (Finset.mem_insert_of_mem hr))

/-- Distinct prime divisors above `L` are bounded once the next power of
`L+1` exceeds the target.  This elementary product lemma is the finite
counting engine for coefficient deduplication. -/
private theorem card_primeDivisors_le_of_lt_pow
    (A : Finset ℕ) (N L d : ℕ) (hN : 0 < N)
    (hprime : ∀ q ∈ A, q.Prime) (hlarge : ∀ q ∈ A, L < q)
    (hdvd : ∀ q ∈ A, q ∣ N) (hpow : N < (L + 1) ^ (d + 1)) :
    A.card ≤ d := by
  by_contra hcard
  have hdcard : d + 1 ≤ A.card := by omega
  have hpowmono : (L + 1) ^ (d + 1) ≤ (L + 1) ^ A.card :=
    Nat.pow_le_pow_right (by omega) hdcard
  have hprodLower : (L + 1) ^ A.card ≤ ∏ q ∈ A, q := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun q hq ↦ hlarge q hq
  have hprodDvd : (∏ q ∈ A, q) ∣ N :=
    primeFinset_prod_dvd A N hprime hdvd
  have hprodUpper : (∏ q ∈ A, q) ≤ N := Nat.le_of_dvd hN hprodDvd
  omega

/-- Every nonempty fibre of a homomorphism from a finite group is a coset of
its kernel.  This private counting lemma is the coordinate mechanism behind
the bounded quadratic fibres; only the resulting reservoir bound will cross
the provider boundary. -/
private theorem card_fiber_eq_card_ker
    {G M : Type*} [Group G] [Fintype G] [Monoid M] [DecidableEq M]
    (f : G →* M) (y : M) (hy : y ∈ Set.range f) :
    (Finset.univ.filter fun x ↦ f x = y).card = Nat.card f.ker := by
  calc
    (Finset.univ.filter fun x ↦ f x = y).card =
        (Finset.univ.filter fun x ↦ f x = 1).card :=
      MonoidHom.card_fiber_eq_of_mem_range f hy ⟨1, map_one f⟩
    _ = (f.ker : Set G).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [MonoidHom.mem_ker]
    _ = Nat.card f.ker := (Nat.card_coe_set_eq (f.ker : Set G)).symm

/-- A square fibre in a finite commutative group has cardinality equal to the
two-torsion kernel whenever it is nonempty. -/
private theorem card_squareFiber_eq_card_twoTorsion
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (y : G)
    (hy : ∃ x : G, x ^ 2 = y) :
    (Finset.univ.filter fun x ↦ x ^ 2 = y).card =
      Nat.card (powMonoidHom 2 : G →* G).ker := by
  apply card_fiber_eq_card_ker (powMonoidHom 2 : G →* G) y
  simpa only [powMonoidHom_apply, Set.mem_range] using hy

/-- Odd prime-power unit square fibres have at most two points.  This is one
branch inside the eventual uniform four-point bound, not a public case split. -/
private theorem oddPrimePower_squareFiber_card_le_two
    {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (hp2 : p ≠ 2)
    (y : (ZMod (p ^ e))ˣ) :
    (Finset.univ.filter fun x ↦ x ^ 2 = y).card ≤ 2 := by
  letI : IsCyclic (ZMod (p ^ e))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  by_cases hy : ∃ x : (ZMod (p ^ e))ˣ, x ^ 2 = y
  · rw [card_squareFiber_eq_card_twoTorsion y hy,
      IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_le_right _ (by omega)
  · simp only [not_exists] at hy
    simp [hy]

namespace SignedInverse

/-- Prime carriers retained from a comparable band after the two intrinsic
current-stage exclusions. -/
def carrierPrimes (Q p n : ℕ) : Finset ℕ :=
  (comparablePrimes n).filter fun b ↦ b < Q ∧ b ≠ p

theorem mem_carrierPrimes_iff {Q p n b : ℕ} :
    b ∈ carrierPrimes Q p n ↔
      n < b ∧ b ≤ 4 * n ∧ b.Prime ∧ b < Q ∧ b ≠ p := by
  simp only [carrierPrimes, Finset.mem_filter, mem_comparablePrimes]
  aesop

/-- One implementation witness for a remote filtered-transverse atom. -/
structure Candidate (Q p : ℕ) (c : PhysicalConstraint) where
  b : ℕ
  pair : ComplementaryPair Q b
  orientation : GoodOrientation p pair
  b_lt : b < Q
  remote : c.obstacleCutoff < pair.start orientation.sign

/-- One prime carrier in the signed-inverse construction.  This is internal
coordinate data; the public output forgets it into a transverse reservoir. -/
structure Carrier (Q p : ℕ) where
  b : ℕ
  prime : b.Prime
  b_lt : b < Q
  coprime : b.Coprime Q

namespace Carrier

/-- Canonical complementary inverse representatives for a carrier. -/
noncomputable def pair {Q p : ℕ} (x : Carrier Q p) (hQ : 1 < Q) :
    ComplementaryPair Q x.b :=
  complementaryPair Q x.b hQ x.prime.one_lt x.b_lt x.coprime

/-- All orientations that are both arithmetically good and physically remote.
No sign selector is introduced. -/
noncomputable def feasibleOrientations
    {Q p : ℕ} (x : Carrier Q p) (hQ : 1 < Q)
    (c : PhysicalConstraint) : Finset Orientation := by
  classical
  exact (x.pair hQ).goodOrientations p |>.filter fun s ↦
    c.obstacleCutoff < (x.pair hQ).start s

theorem mem_feasibleOrientations_iff
    {Q p : ℕ} (x : Carrier Q p) (hQ : 1 < Q)
    (c : PhysicalConstraint) (s : Orientation) :
    s ∈ x.feasibleOrientations hQ c ↔
      s ∈ (x.pair hQ).goodOrientations p ∧
        c.obstacleCutoff < (x.pair hQ).start s := by
  classical
  simp [feasibleOrientations]

/-- Realize one retained orientation as an implementation candidate. -/
noncomputable def candidateOfMem
    {Q p : ℕ} (x : Carrier Q p) (hQ : 1 < Q)
    (c : PhysicalConstraint) (s : Orientation)
    (hs : s ∈ x.feasibleOrientations hQ c) : Candidate Q p c where
  b := x.b
  pair := x.pair hQ
  orientation := (x.pair hQ).goodOrientationOfMem s
    ((x.mem_feasibleOrientations_iff hQ c s).1 hs).1
  b_lt := x.b_lt
  remote := ((x.mem_feasibleOrientations_iff hQ c s).1 hs).2

end Carrier

/-- Convert the retained prime band into the carrier certificate family for a
prime-power current stage. -/
noncomputable def carrierFamily
    {Q p e n : ℕ} (hp : p.Prime) (hQ : Q = p ^ e) :
    Finset (Carrier Q p) := by
  classical
  exact (carrierPrimes Q p n).attach.image fun b ↦
    { b := b.1
      prime := (mem_carrierPrimes_iff.mp b.2).2.2.1
      b_lt := (mem_carrierPrimes_iff.mp b.2).2.2.2.1
      coprime := by
        simpa only [hQ] using hp.coprime_pow_of_not_dvd (m := e) (a := b.1) (by
          intro hpb
          have hpeq : p = b.1 :=
            (Nat.prime_dvd_prime_iff_eq hp
              (mem_carrierPrimes_iff.mp b.2).2.2.1).1 hpb
          exact (mem_carrierPrimes_iff.mp b.2).2.2.2.2 hpeq.symm) }

theorem Carrier.mem_carrierFamily_b
    {Q p e n : ℕ} (hp : p.Prime) (hQ : Q = p ^ e)
    {x : Carrier Q p} (hx : x ∈ carrierFamily (n := n) hp hQ) :
    x.b ∈ carrierPrimes Q p n := by
  classical
  rw [carrierFamily, Finset.mem_image] at hx
  rcases hx with ⟨b, hb, rfl⟩
  exact b.2

/-- The neighboring integer whose prime divisors carry a fixed oriented
coefficient. -/
def coefficientTarget (Q k : ℕ) : Orientation → ℕ
  | .plus => Q * k + 1
  | .minus => Q * k - 1

theorem Carrier.b_injective {Q p : ℕ} :
    Function.Injective (Carrier.b : Carrier Q p → ℕ) := by
  intro x y h
  cases x with
  | mk xb xp xl xc =>
      cases y with
      | mk yb yp yl yc =>
          dsimp at h
          subst yb
          rfl

/-- Prime carriers with one fixed oriented coefficient form a bounded fibre
as soon as the elementary product inequality is supplied. -/
theorem coefficientCarrierFiber_card_le
    {Q p L d k : ℕ} (A : Finset (Carrier Q p)) (hQ : 1 < Q)
    (s : Orientation)
    (hlarge : ∀ x ∈ A, L < x.b)
    (hN : 0 < coefficientTarget Q k s)
    (hpow : coefficientTarget Q k s < (L + 1) ^ (d + 1)) :
    (A.filter fun x ↦ (x.pair hQ).coefficient s = k).card ≤ d := by
  classical
  let F := A.filter fun x ↦ (x.pair hQ).coefficient s = k
  let B := F.image Carrier.b
  have hcard : F.card = B.card := by
    exact (Finset.card_image_of_injective F Carrier.b_injective).symm
  rw [hcard]
  apply card_primeDivisors_le_of_lt_pow B (coefficientTarget Q k s) L d
    hN
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    exact x.prime
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    exact hlarge x (Finset.mem_filter.mp hx).1
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    have hcoeff : (x.pair hQ).coefficient s = k :=
      (Finset.mem_filter.mp hx).2
    cases s with
    | plus =>
        simpa [coefficientTarget, hcoeff] using
          (x.pair hQ).carrier_dvd_coefficientTarget Orientation.plus
    | minus =>
        simpa [coefficientTarget, hcoeff] using
          (x.pair hQ).carrier_dvd_coefficientTarget Orientation.minus
  · exact hpow

/-- In the comparable prime band `(n,4n]`, the coefficient fibre is at most
four once the single explicit scale inequality `(Q²+1)<(n+1)^5` holds. -/
theorem carrierFamily_coefficientFiber_card_le_four
    {Q p e n k : ℕ} (hp : p.Prime) (hQ : Q = p ^ e)
    (hstage : 1 < Q) (s : Orientation)
    (hN : 0 < coefficientTarget Q k s)
    (hscale : Q ^ 2 + 1 < (n + 1) ^ 5) :
    ((carrierFamily (n := n) hp hQ).filter fun x ↦
      (x.pair hstage).coefficient s = k).card ≤ 4 := by
  classical
  let A := carrierFamily (n := n) hp hQ
  let F := A.filter fun x ↦ (x.pair hstage).coefficient s = k
  by_cases hF : F.Nonempty
  · rcases hF with ⟨x, hx⟩
    have hxA : x ∈ A := (Finset.mem_filter.mp hx).1
    have hxcoeff : (x.pair hstage).coefficient s = k :=
      (Finset.mem_filter.mp hx).2
    have htarget : coefficientTarget Q k s < Q ^ 2 + 1 := by
      cases s with
      | plus =>
          simpa [coefficientTarget, hxcoeff] using
            (x.pair hstage).coefficientTarget_lt_sq_add_one x.b_lt
              Orientation.plus
      | minus =>
          simpa [coefficientTarget, hxcoeff] using
            (x.pair hstage).coefficientTarget_lt_sq_add_one x.b_lt
              Orientation.minus
    apply coefficientCarrierFiber_card_le A hstage s
    · intro y hy
      exact (mem_carrierPrimes_iff.mp
        (Carrier.mem_carrierFamily_b hp hQ hy)).1
    · exact hN
    · exact lt_trans htarget hscale
  · have hzero : F.card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hF)
    change F.card ≤ 4
    omega

namespace Candidate

/-- Forget a candidate's coordinates and retain only its physical support. -/
def support {Q p : ℕ} {c : PhysicalConstraint}
    (x : Candidate Q p c) (hQpos : 0 < Q) : Support :=
  x.orientation.atom hQpos

theorem admissible {Q p : ℕ} {c : PhysicalConstraint}
    (x : Candidate Q p c) (hQpos : 0 < Q) :
    (x.support hQpos).Admissible smallBlockSizes c :=
  binaryBlock_admissible c
    ⟨x.pair.start x.orientation.sign,
      x.pair.start_pos hQpos x.orientation.sign⟩ x.remote

theorem filteredTransverse {Q p e : ℕ} {c : PhysicalConstraint}
    (x : Candidate Q p c) (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) :
    (x.support (hQ.symm ▸ pow_pos hp.pos e)).FilteredTransverse Q :=
  atom_filteredTransverse x.orientation hp he hQ x.b_lt

@[simp]
theorem grade {Q p : ℕ} {c : PhysicalConstraint}
    (x : Candidate Q p c) (hQpos : 0 < Q) :
    (x.support hQpos).grade = 1 :=
  binaryBlock_grade _

end Candidate

/-- Realize every feasible orientation of every carrier.  The construction is
a finite union of feasibility sets, never a chosen-sign image. -/
noncomputable def candidateFamily
    {Q p : ℕ} (A : Finset (Carrier Q p)) (hQ : 1 < Q)
    (c : PhysicalConstraint) : Finset (Candidate Q p c) := by
  classical
  exact A.biUnion fun x ↦
    (x.feasibleOrientations hQ c).attach.image fun s ↦
      x.candidateOfMem hQ c s.1 s.2

/-- A finite witness family realizes an intrinsic transverse reservoir. -/
noncomputable def reservoir
    {Q p e : ℕ} {c : PhysicalConstraint}
    (A : Finset (Candidate Q p c)) (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e) : TransverseReservoir Q c := by
  classical
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  refine
    { atoms := A.image fun x ↦ x.support hQpos
      admissible := ?_
      transverse := ?_ }
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, hx, rfl⟩
    exact x.admissible hQpos
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, hx, rfl⟩
    exact x.filteredTransverse hp he hQ

/-- Pairwise-compatible witnesses realize the intrinsic compatible pool. -/
noncomputable def compatiblePool
    {Q p e : ℕ} {c : PhysicalConstraint}
    (A : Finset (Candidate Q p c)) (hp : p.Prime) (he : 0 < e)
    (hQ : Q = p ^ e)
    (hcompat : ∀ x ∈ A, ∀ y ∈ A,
      x.support (hQ.symm ▸ pow_pos hp.pos e) ≠
        y.support (hQ.symm ▸ pow_pos hp.pos e) →
      (x.support (hQ.symm ▸ pow_pos hp.pos e)).CompatibleFor
        (y.support (hQ.symm ▸ pow_pos hp.pos e)) c) :
    CompatibleTransversePool Q c := by
  classical
  let hQpos : 0 < Q := hQ.symm ▸ pow_pos hp.pos e
  let R := reservoir A hp he hQ
  refine
    { toTransverseReservoir := R
      compatible := ?_ }
  intro S hS T hT hST
  rcases Finset.mem_image.mp hS with ⟨x, hx, rfl⟩
  rcases Finset.mem_image.mp hT with ⟨y, hy, rfl⟩
  exact hcompat x hx y hy hST

end SignedInverse
end Erdos289
