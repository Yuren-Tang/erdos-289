module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.SignedInverseAtom

@[expose] public section

/-!
# Rank truncation of a row

The row certificate keeps only the upper half of the row by coefficient rank.
That step is pure pigeonhole — fewer than half of a finite set of naturals can
lie below half its cardinality — and the resulting centre and mass bounds are
then exact consequences of the inverse equation.

Nothing here is chosen: the threshold is the cardinality of the row itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/--
At least half of a finite set of naturals is at least half its cardinality.
This is the rank truncation: the retained coefficients are as large as the row
is long.
-/
theorem card_upperRank_ge (S : Finset ℕ) :
    S.card - S.card / 2 ≤ (S.filter fun k => S.card / 2 ≤ k).card := by
  classical
  have hsub : (S.filter fun k => ¬ S.card / 2 ≤ k) ⊆ Finset.range (S.card / 2) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨-, hlt⟩
    exact Finset.mem_range.mpr (by omega)
  have hle : (S.filter fun k => ¬ S.card / 2 ≤ k).card ≤ S.card / 2 := by
    refine le_trans (Finset.card_le_card hsub) ?_
    simp
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := S) (p := fun k => S.card / 2 ≤ k)
  omega

/-- A large coefficient forces a remote distinguished centre. -/
theorem le_start_of_le_coefficient
    {Q b : ℕ} (w : ComplementaryPair Q b) (s : Orientation)
    {m : ℕ} (hm : m ≤ w.coefficient s) :
    Q * m - 1 ≤ w.start s := by
  have hmono : Q * m ≤ Q * w.coefficient s := Nat.mul_le_mul_left _ hm
  have hle := w.distinguished_le_start_succ s
  omega

/--
The exact mass bound of the row certificate: an atom whose coefficient is at
least `m` has reciprocal value below `2 / (Q m - 1)`.
-/
theorem GoodOrientation.atom_value_lt_of_le_coefficient
    {Q b p : ℕ} {w : ComplementaryPair Q b} (g : GoodOrientation p w) (hQ : 0 < Q)
    {m : ℕ} (hm : m ≤ w.coefficient g.sign) (hpos : 1 < Q * m) :
    (g.atom hQ).value < 2 / ((Q * m - 1 : ℕ) : ℚ) := by
  have hstart : Q * m - 1 ≤ w.start g.sign := le_start_of_le_coefficient w g.sign hm
  have hposQ : (0 : ℚ) < ((Q * m - 1 : ℕ) : ℚ) := by
    have : 0 < Q * m - 1 := by omega
    exact_mod_cast this
  have hcast : ((Q * m - 1 : ℕ) : ℚ) ≤ ((w.start g.sign : ℕ) : ℚ) := by
    exact_mod_cast hstart
  calc (g.atom hQ).value < 2 / ((w.start g.sign : ℕ) : ℚ) :=
        g.atom_value_lt_two_div_start hQ
    _ ≤ 2 / ((Q * m - 1 : ℕ) : ℚ) := by
        exact div_le_div_of_nonneg_left (by norm_num) hposQ hcast

end SignedInverse
end Erdos289
