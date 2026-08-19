module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.Selector
public import Erdos289.PhysicalSupports
public import AffineCorrection.CompactResolution
public import AffineCorrection.Transfer

@[expose] public section

/-!
# Instantiating the universal core at the reciprocal system

The universal theorem of `AffineCorrection/` is stated for an arbitrary
observation system, physical partial monoid, exact-value map and grade map.
This module fixes those data for Erdős 289 and identifies the universal
conclusion with the statement the descent needs.

* the exact value group is the centered group `ℚ/ℤ`, so the target residue is
  zero and no separate translation bookkeeping survives;
* the observation index category is the poset of compact stages of `ℚ/ℤ`, and
  the observation system is the canonical quotient one;
* the physical system is the path-support partial commutative monoid, on which
  exact reciprocal value and connected-component grade are already proved
  additive;
* the physical family is the admissible supports lying in the selector interval
  `(0, 2)`.

With these choices, `AffineCorrection.exactSpectrum` at the target residue `0`
is literally the set of grades carried by exact reciprocal representations of
`1`, which is what `Erdos289.CofiniteSaturation` quantifies over.

## The two hypotheses of the universal theorem

`AffineCorrection.grade_mem_exactSpectrum_of_covers_target` takes two
hypotheses, and this module supplies neither; both are theorems about the
arithmetic of the reciprocal system rather than about the identification made
here.

`LiteralizesTarget` at a compact stage `H` says that a target realizer's
residue is *exactly* zero, whereas the pullback only gives residue in `H`.  The
gap between the two is a fixed finite defect subgroup, and it closes once the
endpoint stages eventually contain that subgroup; `AffineCorrection.LeastAbsorber`
is the universal object of that absorption.  `Covers` is the local-profile
statement of the arithmetic layers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The canonical observation system: compact quotient stages of `ℚ/ℤ`. -/
noncomputable def reciprocalObservation :
    AffineCorrection.ObservationSystem
      (AffineCorrection.CompactStage TargetResidue) TargetResidue :=
  AffineCorrection.CompactResolution.system TargetResidue

/--
The physical family used by the descent: admissible supports whose exact value
lies in the selector interval `(0, 2)`.

The interval is not a safety margin.  Its endpoints are the two lifts of the
target residue adjacent to the target, which is exactly what makes the centered
condition pin the value; see `Erdos289/Selector.lean`.
-/
def selectorFamily (c : PhysicalConstraint) : Set Support :=
  {S | S.Admissible smallBlockSizes c ∧ 0 < S.value ∧ S.value < 2}

theorem mem_selectorFamily_iff {c : PhysicalConstraint} {S : Support} :
    S ∈ selectorFamily c ↔
      S.Admissible smallBlockSizes c ∧ 0 < S.value ∧ S.value < 2 :=
  Iff.rfl

/--
The universal conclusion, read in the reciprocal system: a grade in the exact
spectrum of the selector family at residue zero is a grade carried by an exact
representation of `1`.
-/
noncomputable def saturationWitness_of_mem_exactSpectrum
    {c : PhysicalConstraint} {k : ℕ}
    (h : k ∈ AffineCorrection.exactSpectrum (selectorFamily c)
      Support.residue Support.grade 0) :
    SaturationWitness smallBlockSizes 1 c k :=
  saturationWitness_of_residue_zero
    (Classical.choose_spec h).1.1
    (Classical.choose_spec h).2.2
    (Classical.choose_spec h).1.2.1
    (Classical.choose_spec h).1.2.2
    (Classical.choose_spec h).2.1

/--
Cofinite saturation is exactly cofiniteness of the exact spectrum of the
selector family at residue zero.
-/
theorem cofiniteSaturation_of_exactSpectrum
    {c : PhysicalConstraint} {N : ℕ}
    (h : ∀ k, N ≤ k → k ∈ AffineCorrection.exactSpectrum (selectorFamily c)
      Support.residue Support.grade 0) :
    CofiniteSaturation smallBlockSizes 1 c :=
  ⟨N, fun k hk => ⟨saturationWitness_of_mem_exactSpectrum (h k hk)⟩⟩

/-- Exact reciprocal value is additive on the physical partial monoid. -/
theorem isAdditiveOn_value :
    AffineCorrection.IsAdditiveOn supportPCM Support.value :=
  support_value_additive

/-- Connected-component grade is additive on the physical partial monoid. -/
theorem isAdditiveOn_grade :
    AffineCorrection.IsAdditiveOn supportPCM Support.grade :=
  support_grade_additive

/-- Centered residue is additive on the physical partial monoid. -/
theorem isAdditiveOn_residue :
    AffineCorrection.IsAdditiveOn supportPCM Support.residue := by
  intro a b c hadd
  change AffineCorrection.CenteredValue.mk (1 : ℚ) c.value = _
  rw [support_value_additive hadd, map_add]
  rfl

end Erdos289
