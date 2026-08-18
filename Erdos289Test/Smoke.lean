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

/-!
### Faithfulness of the literal statements

These two examples restate the target sentences verbatim and check that the
definitions in `Erdos289/Literal.lean` are the same propositions, so that the
derivations in that file cannot silently drift away from what they claim to
formalize.  The first is the right-hand side of `erdos_289` in
`google-deepmind/formal-conjectures`, copied as written there.
-/

example : Erdos289.Erdos289Literal ↔
    (∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 < (I j).1 ∨ (I j).2 < (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) :=
  Iff.rfl

/-- The erdosproblems.com wording, which also forbids adjacent intervals. -/
example : Erdos289.Erdos289LiteralSeparated ↔
    (∀ᶠ k : ℕ in Filter.atTop, ∃ I : Fin k → ℕ × ℕ,
    (∀ i, (I i).1 < (I i).2) ∧
    (∀ i j, i ≠ j → (I i).2 + 1 < (I j).1 ∨ (I j).2 + 1 < (I i).1) ∧
    ∑ i, ∑ n ∈ Finset.Icc (I i).1 (I i).2, (n⁻¹ : ℚ) = 1) :=
  Iff.rfl

example (h : Erdos289.Erdos289Statement) : Erdos289.Erdos289Literal :=
  Erdos289.erdos289Literal_of_statement h

end Erdos289Test
