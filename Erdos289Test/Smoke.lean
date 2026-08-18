module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289Test

example : Erdos289.RemoteLightNeutralGradeOne :=
  Erdos289.remoteLightNeutralGradeOne

example (hE : Erdos289.UnitFractionRefinementCofinality)
    (q : ℚ) (hq : 0 < q) (c : Erdos289.PhysicalConstraint) :
    Nonempty (Erdos289.RationalPresentation q c) :=
  Erdos289.rationalPresentation_of_pos hE q hq c

example (a : Erdos289.Denominator) :
    (Erdos289.ternaryBlock a).value =
      (Erdos289.binaryBlock (a + 1)).value + Erdos289.reciprocal a :=
  Erdos289.endpoint_inclusion_switch a

example (hE : Erdos289.UnitFractionRefinementCofinality)
    (q : ℚ) (hq : 0 < q) (c : Erdos289.PhysicalConstraint) :
    Nonempty (Erdos289.SameGradeDeformation q c) :=
  Erdos289.endpointDeformation_of_unitFractionRefinement hE q hq c

example (hE : Erdos289.UnitFractionRefinementCofinality) :
    Erdos289.ArbitrarilyLightMobility :=
  Erdos289.arbitrarilyLightMobility_of_refinement_neutral hE
    Erdos289.remoteLightNeutralGradeOne

example : Erdos289.UnitFractionRefinementCofinality :=
  Erdos289.unitFractionRefinementCofinality

example : Erdos289.ArbitrarilyLightMobility :=
  Erdos289.arbitrarilyLightMobility

example {p : ℕ} [Fact p.Prime]
    (A : Finset (ZMod p)) (h : ℕ)
    (hA : A.Nonempty) (hh : h ≤ A.card) :
    min p (h * (A.card - h) + 1) ≤
      (Erdos289.RestrictedFold.image A h).card :=
  Erdos289.RestrictedFold.image_card_lower_bound A h hA hh

example {V I : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (pools : I → Finset V)
    (hpartition : Erdos289.IndependentTransversal.IsPoolPartition pools)
    (hthick : ∀ i, 2 * G.maxDegree ≤ (pools i).card) :
    Erdos289.IndependentTransversal.HasChunkPacking G pools :=
  Erdos289.IndependentTransversal.hasChunkPacking_of_two_mul_maxDegree_le
    G pools hpartition hthick

end Erdos289Test
