module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.AtomClass

@[expose] public section

/-!
# A prime row has simple-fibre multiplicity one

At a prime current the coefficients of a row are positive and below the
carrier, hence below `p`, so distinct coefficients are already distinct modulo
`p`.  By `Erdos289.SignedInverse.atom_simpleFibreClass_eq_iff` — which pins an
atom's class by the equation `k • class = generator`, uniformly in the exponent
— distinct coefficients therefore give distinct classes.

Consequently a deduplicated prime row injects into the simple fibre, and the
image that feeds the Dias da Silva–Hamidoune interval is as large as the row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/--
Distinct current coefficients give distinct simple-fibre classes at a prime
current.
-/
theorem atom_simpleFibreClass_ne_of_coefficient_ne
    {p b b' : ℕ} {w : ComplementaryPair p b} {w' : ComplementaryPair p b'}
    (hp : p.Prime) (g : GoodOrientation p w) (g' : GoodOrientation p w')
    (hppos : 0 < p) (hb : b < p) (hb' : b' < p)
    (hne : w.coefficient g.sign ≠ w'.coefficient g'.sign)
    (hfac : (g.atom hppos).FactorsThroughPrimePowerStage p)
    (hfac' : (g'.atom hppos).FactorsThroughPrimePowerStage p) :
    (g.atom hppos).simpleFibreClass hfac ≠ (g'.atom hppos).simpleFibreClass hfac' := by
  have hk := coefficient_pos_lt w g.sign
  have hk' := coefficient_pos_lt w' g'.sign
  intro heq
  have hcast :=
    (atom_simpleFibreClass_eq_iff hp Nat.one_pos (pow_one p).symm g g'
      hppos hb hb' hfac hfac').1 heq
  refine hne ?_
  have h1 : w.coefficient g.sign < p := lt_trans hk.2 hb
  have h2 : w'.coefficient g'.sign < p := lt_trans hk'.2 hb'
  have := congrArg ZMod.val hcast
  rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this

end SignedInverse
end Erdos289
