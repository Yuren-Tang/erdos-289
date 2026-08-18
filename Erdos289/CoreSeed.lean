module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.Descent
public import Erdos289.LightMobility

@[expose] public section

/-!
# The finite core stage, constructed

The core provider of the manuscript is a *generic finite torsor seed*: pick a
finite cyclic residue group, realize a complete sequence for it by
arbitrarily-light equal-grade switches placed one beyond another, and read off
the Boolean family of their joint states.

The complete sequence used here is the simplest one, `c₁ = ⋯ = c_{D-1} = 1`:
its subset sums are `{0, 1, …, D-1}`, which is exactly what completeness asks
for.  The manuscript's binary sequence is shorter, but length is not part of
the theorem — the seed footprint only has to be finite — and the mass bound is
the same either way, because the maximal subset sum is `(D-1)/D` in both cases.

So a ladder of `D - 1` equal-grade switches of increment `1/D`, each placed
beyond the previous one's footprint and each arbitrarily light, has states of

* one common grade,
* mass `β + j/D` for `j = 0, …, D - 1` with `0 < β` arbitrarily small,
* residues `ρ(β) + j·[1/D]`, i.e. one complete torsor under `⟨[1/D]⟩`.

With `β < 1/2` the barrier slack is `1/2 > 0`, and the seed *is* a `CoreStage`.
No lcm bridge is needed for this interface: enlarging the core subgroup only
moves work from the tail provider to the core provider, and the descent spine
does not care which side does it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-! ### An elementary fact -/

/-- An arbitrarily light *positive* admissible state, from light mobility. -/
theorem exists_lightPositive (c : PhysicalConstraint) {ε : ℚ} (hε : 0 < ε) :
    ∃ P : Support, P.Admissible smallBlockSizes c ∧ 0 < P.value ∧ P.value < ε := by
  obtain ⟨w⟩ := arbitrarilyLightMobility (ε / 2) (by linarith) c (ε / 2) (by linarith)
  refine ⟨w.upper, w.upper_admissible, ?_, ?_⟩
  · rw [w.value_eq]
    have := Support.value_nonneg w.lower
    linarith
  · rw [w.value_eq]
    have := w.lower_value_lt
    linarith

/-! ### The ladder of equal-grade switches -/

/--
`n` equal-grade switches of increment `q`, placed one beyond another: the state
with `j` switches raised has mass `base + j q`, and all states share one grade
and one footprint.
-/
structure Ladder (c : PhysicalConstraint) (q : ℚ) (n : ℕ) (ε : ℚ) where
  state : ℕ → Support
  footprint : Support
  grade : ℕ
  base : ℚ
  subset : ∀ j, j ≤ n → state j ⊆ footprint
  admissible : ∀ j, j ≤ n → (state j).Admissible smallBlockSizes c
  grade_eq : ∀ j, j ≤ n → (state j).grade = grade
  value_eq : ∀ j, j ≤ n → (state j).value = base + j * q
  base_pos : 0 < base
  base_lt : base < ε

theorem exists_ladder (c : PhysicalConstraint) {q : ℚ} (hq : 0 < q) :
    ∀ (n : ℕ) {ε : ℚ}, 0 < ε → Nonempty (Ladder c q n ε) := by
  intro n
  induction n with
  | zero =>
      intro ε hε
      obtain ⟨P, hPadm, hPpos, hPlt⟩ := exists_lightPositive c hε
      refine ⟨{
        state := fun _ => P
        footprint := P
        grade := P.grade
        base := P.value
        subset := fun _ _ => Finset.Subset.refl P
        admissible := fun _ _ => hPadm
        grade_eq := fun _ _ => rfl
        value_eq := fun j hj => by
          have : j = 0 := Nat.le_zero.mp hj
          subst this
          simp
        base_pos := hPpos
        base_lt := hPlt }⟩
  | succ n ih =>
      intro ε hε
      obtain ⟨L⟩ := ih (ε := ε / 2) (by linarith)
      obtain ⟨w⟩ := arbitrarilyLightMobility q hq
        (constraintBeyond c L.footprint) (ε / 2) (by linarith)
      classical
      have hlowAvoid := w.lower_admissible.2.1
      have huppAvoid := w.upper_admissible.2.1
      refine ⟨{
        state := fun j => if j ≤ n then L.state j ∪ w.lower else L.state n ∪ w.upper
        footprint := (L.footprint ∪ w.lower) ∪ w.upper
        grade := L.grade + w.lower.grade
        base := L.base + w.lower.value
        subset := ?_
        admissible := ?_
        grade_eq := ?_
        value_eq := ?_
        base_pos := ?_
        base_lt := ?_ }⟩
      · intro j _
        by_cases hj : j ≤ n <;> simp only [hj, if_true, if_false]
        · refine Finset.union_subset ?_ ?_
          · exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ (L.subset j hj hx))
          · exact fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        · refine Finset.union_subset ?_ ?_
          · exact fun x hx =>
              Finset.mem_union_left _ (Finset.mem_union_left _ (L.subset n le_rfl hx))
          · exact fun x hx => Finset.mem_union_right _ hx
      · intro j _
        by_cases hj : j ≤ n <;> simp only [hj, if_true, if_false]
        · exact admissible_union_of_pairBeyond c (F := L.footprint) (L.subset j hj)
            (L.admissible j hj) w.lower_admissible
        · exact admissible_union_of_pairBeyond c (F := L.footprint) (L.subset n le_rfl)
            (L.admissible n le_rfl) w.upper_admissible
      · intro j _
        by_cases hj : j ≤ n <;> simp only [hj, if_true, if_false]
        · rw [grade_union_of_pairBeyond c (F := L.footprint) (L.subset j hj) hlowAvoid,
            L.grade_eq j hj]
        · rw [grade_union_of_pairBeyond c (F := L.footprint) (L.subset n le_rfl) huppAvoid,
            L.grade_eq n le_rfl, w.grade_eq]
      · intro j hj
        by_cases hjn : j ≤ n <;> simp only [hjn, if_true, if_false]
        · rw [value_union_of_pairBeyond c (F := L.footprint) (L.subset j hjn) hlowAvoid,
            L.value_eq j hjn]
          ring
        · have hje : j = n + 1 := by omega
          subst hje
          rw [value_union_of_pairBeyond c (F := L.footprint) (L.subset n le_rfl) huppAvoid,
            L.value_eq n le_rfl, w.value_eq]
          push_cast
          ring
      · have := Support.value_nonneg w.lower
        have := L.base_pos
        linarith
      · have := L.base_lt
        have := w.lower_value_lt
        linarith

/-! ### Reading a finite cyclic torsor off the ladder -/

/-- Every element of a cyclic group of exponent `D` is a small natural multiple
of its generator. -/
theorem exists_lt_nsmul_of_mem_zmultiples
    {A : Type*} [AddCommGroup A] {a : A} {D : ℕ} (hD : 0 < D) (hord : D • a = 0)
    {u : A} (hu : u ∈ AddSubgroup.zmultiples a) :
    ∃ j : ℕ, j < D ∧ u = j • a := by
  rw [AddSubgroup.mem_zmultiples_iff] at hu
  obtain ⟨z, rfl⟩ := hu
  have hDz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnn : 0 ≤ z % (D : ℤ) := Int.emod_nonneg z hDz
  have hlt : z % (D : ℤ) < (D : ℤ) := Int.emod_lt_of_pos z (by exact_mod_cast hD)
  have hcast : ((z % (D : ℤ)).toNat : ℤ) = z % (D : ℤ) := Int.toNat_of_nonneg hnn
  have hD0 : ((D : ℤ)) • a = 0 := by rw [natCast_zsmul]; exact hord
  refine ⟨(z % (D : ℤ)).toNat, ?_, ?_⟩
  · have : ((z % (D : ℤ)).toNat : ℤ) < (D : ℤ) := by rw [hcast]; exact hlt
    exact_mod_cast this
  · have hsplit : (D : ℤ) * (z / (D : ℤ)) + z % (D : ℤ) = z := Int.mul_ediv_add_emod z (D : ℤ)
    calc z • a = ((D : ℤ) * (z / (D : ℤ)) + z % (D : ℤ)) • a := by rw [hsplit]
      _ = ((D : ℤ) * (z / (D : ℤ))) • a + (z % (D : ℤ)) • a := add_zsmul a _ _
      _ = (z % (D : ℤ)) • a := by rw [mul_zsmul', hD0, smul_zero, zero_add]
      _ = ((z % (D : ℤ)).toNat : ℕ) • a := by rw [← natCast_zsmul, hcast]

/-! ### The core stage -/

/--
The generic finite torsor seed is a core stage: for every `D ≥ 1` and every
physical constraint there is a `CoreStage` whose subgroup is the cyclic group
generated by `[1/D]` and whose barrier slack is `1/2`.
-/
theorem exists_coreStage (c : PhysicalConstraint) {D : ℕ} (hD : 0 < D) :
    ∃ B : CoreStage c,
      B.subgroup = AddSubgroup.zmultiples (reciprocalResidue ⟨D, hD⟩) ∧
        B.slack = 1 / 2 := by
  classical
  have hord : D • reciprocalResidue ⟨D, hD⟩ = 0 :=
    (nsmul_reciprocalResidue_eq_zero_iff D ⟨D, hD⟩).2 dvd_rfl
  have hDQ : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hqpos : (0 : ℚ) < 1 / (D : ℚ) := by positivity
  obtain ⟨L⟩ := exists_ladder c hqpos (D - 1) (ε := 1 / 2) (by norm_num)
  refine ⟨{
    subgroup := AddSubgroup.zmultiples (reciprocalResidue ⟨D, hD⟩)
    centre := AffineCorrection.CenteredValue.mk (1 : ℚ) L.base
    grade := L.grade
    footprint := L.footprint
    slack := 1 / 2
    slack_pos := by norm_num
    covers := ?_ }, rfl, rfl⟩
  intro u hu
  obtain ⟨j, hjD, rfl⟩ := exists_lt_nsmul_of_mem_zmultiples hD hord hu
  have hjle : j ≤ D - 1 := by omega
  have hjq : (0 : ℚ) ≤ (j : ℚ) * (1 / (D : ℚ)) := by positivity
  have hjq1 : (j : ℚ) * (1 / (D : ℚ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hDQ]
    exact_mod_cast hjD.le
  refine ⟨L.state j, L.subset j hjle, L.admissible j hjle, L.grade_eq j hjle, ?_, ?_, ?_⟩
  · have hval : (L.state j).residue
        = AffineCorrection.CenteredValue.mk (1 : ℚ) (L.base + (j : ℚ) * (1 / (D : ℚ))) := by
      rw [Support.residue, L.value_eq j hjle]
    rw [hval, map_add]
    congr 1
  · rw [L.value_eq j hjle]
    linarith [L.base_pos]
  · rw [L.value_eq j hjle]
    linarith [L.base_lt]

/--
Erdős 289 from the tail interface alone.

The core interface is discharged by `exists_coreStage`, so the only remaining
obligation is the manuscript's cofinal tail: beyond any finite footprint, and
for any target class, states of every large grade whose residues cover the
ambient group modulo the core's cyclic subgroup, with total load below the
barrier slack `1/2`.
-/
theorem erdos289Statement_of_tailInterface
    {D : ℕ} (hD : 0 < D)
    (hsupply : ∀ (F : Support) (τ : TargetResidue), ∃ N : ℕ, ∀ h, N ≤ h →
      ∃ (G : AddSubgroup TargetResidue) (ε : ℚ),
        τ ∈ G ∧ ε < 1 / 2 ∧
        TailCovers originalConstraint F
          (AddSubgroup.zmultiples (reciprocalResidue ⟨D, hD⟩)) G h ε) :
    Erdos289Statement := by
  obtain ⟨B, hsub, hslack⟩ := exists_coreStage originalConstraint hD
  obtain ⟨N, hN⟩ := hsupply B.footprint B.centre
  refine cofiniteSaturation_one_of_core_tail B (N := N) ?_
  intro h hh
  obtain ⟨G, ε, hτ, hε, htail⟩ := hN h hh
  refine ⟨G, ε, hτ, ?_, ?_⟩
  · rw [hslack]; exact hε
  · rw [hsub]; exact htail

end Erdos289
