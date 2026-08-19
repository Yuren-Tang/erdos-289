module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.CurrentStage
public import Erdos289.RowReservoir
public import Erdos289.ChunkPartition

@[expose] public section

/-!
# A band of carriers is a tail stage, at any prime-power current

The row certificate is parametric in the current, and so is the padding
mechanism, so the passage from a band of carriers to one link of the tail chain
never has to distinguish a prime from a proper prime power.

The padding is placed at the far end of the current, just below `Q`, so that it
is the lighter part of the stage rather than the heavier one, and so that it
stays clear of the row's atoms, which sit near `Q t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/--
One current, end to end, by the padding mechanism.

The parameters are the row certificate's — the band ratio `Λ`, the
coefficient-fibre scale `d`, the truncation rank `t` — together with the
surviving size `m` and the grade `h`.  The three conditions on them are the
supply inequality, the pigeonhole threshold `(p-1)(p-2) < m`, and the room
below the current for `h` padding blocks clear of the row.
-/
theorem exists_tailStage_of_band_padded
    {Λ Q p e n d t m h : ℕ} {c : PhysicalConstraint}
    (hΛ : 0 < Λ) (hd : 0 < d) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e) (hQ1 : 1 < Q)
    (A : Finset (Carrier Q p))
    (hA : A ⊆ carrierFamily (Λ := Λ) (n := n) hp hQ)
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ Q p (bandBase Λ Q))
    (hscale : Q ^ 2 + 1 < (n + 1) ^ (d + 1))
    (hpos : 1 < Q * t) (hm : 0 < m)
    (hsupply :
      4 * (Λ - 1)
        + 2 * d * (m * (4 * (max 1 c.separation + 1)) + t + 2 * c.obstacle.card)
        ≤ A.card)
    (hstock : (p - 1) * (p - 2) < m)
    (hph : p - 1 ≤ h)
    (hroom : c.obstacleCutoff + h * paddingSpacing c + 3 < Q)
    (hfar : max 1 c.separation < Q * (t - 1)) :
    ∃ F : Support,
      TailStage c F (lowerPrimePowerStage Q) (primePowerStage Q) h
        (h * (2 / ((Q - h * paddingSpacing c - 2 : ℕ) : ℚ))) := by
  classical
  set K := 4 * (max 1 c.separation + 1) with hK
  have hKpos : 0 < K := by positivity
  set base := Q - h * paddingSpacing c - 2 with hbaseDef
  have hbase : 0 < base := by omega
  have hcut : c.obstacleCutoff < base := by omega
  have hfit : base + h * paddingSpacing c + 1 < Q := by omega
  -- the reservoir of the row
  obtain ⟨R, starts, hatoms, hstartlb, hcard, hmassR⟩ :=
    exists_rowReservoir (Λ := Λ) (n := n) (d := d) (t := t) (c := c)
      hΛ hp he hQ hQ1 A hA hband hscale hpos
  -- the surviving row is large enough to pack into `m` chunks
  have hrow : m * K ≤ R.atoms.card := by
    have hchain : 2 * d * (m * K + t + 2 * c.obstacle.card)
        ≤ 2 * d * (R.atoms.card + t + 2 * c.obstacle.card) := by
      have h1 : 2 * d * (m * K + t + 2 * c.obstacle.card) ≤ A.card - 4 * (Λ - 1) := by
        omega
      omega
    have hdpos : 0 < 2 * d := by omega
    have := Nat.le_of_mul_le_mul_left hchain hdpos
    omega
  obtain ⟨P, hPsub, hPcard⟩ :=
    exists_compatiblePool_of_binary_of_card R starts hatoms
      (by calc K = 1 * K := (one_mul K).symm
        _ ≤ m * K := Nat.mul_le_mul_right _ hm
        _ ≤ R.atoms.card := hrow)
  have hmP : m ≤ P.atoms.card := by
    have hlt : m * K < (P.atoms.card + 1) * K := lt_of_le_of_lt hrow hPcard
    have := Nat.lt_of_mul_lt_mul_right hlt
    omega
  -- every pool atom is a binary block of the row
  have hbinary : ∀ S ∈ P.atoms, ∃ a ∈ starts, S = binaryBlock a := by
    intro S hS
    have := hPsub hS
    rw [hatoms] at this
    rcases Finset.mem_image.mp this with ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  have hgradeP : ∀ S ∈ P.atoms, S.grade = 1 := by
    intro S hS
    obtain ⟨a, -, rfl⟩ := hbinary S hS
    exact binaryBlock_grade _
  -- the padding is lighter than nothing else in the stage
  have hbaseQ : ((base : ℕ) : ℚ) ≤ ((Q * t - 1 : ℕ) : ℚ) := by
    have : base ≤ Q * t - 1 := by
      have h1 : 1 ≤ t := by
        by_contra hcon
        have ht0 : t = 0 := by omega
        subst ht0
        omega
      have : Q ≤ Q * t := Nat.le_mul_of_pos_right _ (by omega)
      omega
    exact_mod_cast this
  have hbaseR : (0 : ℚ) < ((base : ℕ) : ℚ) := by exact_mod_cast hbase
  have hmassP : ∀ S ∈ P.atoms, S.value ≤ 2 / ((base : ℕ) : ℚ) := by
    intro S hS
    refine le_of_lt (lt_of_lt_of_le (hmassR S (hPsub hS)) ?_)
    exact div_le_div_of_nonneg_left (by norm_num) hbaseR hbaseQ
  -- the padding stays clear of the row
  have hcross : ∀ S ∈ P.atoms, ∀ T ∈ paddingBlocks c base hbase h,
      S.CompatibleFor T c := by
    intro S hS T hT
    obtain ⟨a, ha, rfl⟩ := hbinary S hS
    obtain ⟨i, hi, rfl⟩ := (mem_paddingBlocks hbase).1 hT
    have halb := hstartlb a ha
    have hiub : i * paddingSpacing c ≤ h * paddingSpacing c :=
      Nat.mul_le_mul_right _ (le_of_lt hi)
    have hdist : max 1 c.separation + 1 <
        Nat.dist a.1 ((⟨base + i * paddingSpacing c, by omega⟩ : Denominator)).1 := by
      show max 1 c.separation + 1 < Nat.dist a.1 (base + i * paddingSpacing c)
      rw [Nat.dist]
      have h1 : 1 ≤ t := by
        by_contra hcon
        have ht : t = 0 := by omega
        subst ht
        omega
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hQt : Q + Q * (t' + 1 - 1) = Q * (t' + 1) := by
        rw [Nat.add_sub_cancel, Nat.mul_succ]
        omega
      omega
    exact ⟨crossSeparated_graphDisjoint
        (binaryBlock_crossSeparated_of_dist (m := 1) (lt_of_le_of_lt (by omega) hdist)),
      binaryBlock_crossSeparated_of_dist (m := c.separation)
        (lt_of_le_of_lt (by omega) hdist)⟩
  exact exists_tailStage_of_pool_and_padding P hp he hQ hbase hcut hfit hcross
    (by omega) hph hmassP le_rfl hgradeP

end SignedInverse
end Erdos289
