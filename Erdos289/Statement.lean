module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PathSupport
public import AffineCorrection.CofinalIntervals
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Final mathematical statements

The statements are phrased only in terms of exact reciprocal value, the
connected-component quotient, and finite physical constraints.  They do not
mention any provider coordinates or implementation certificates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- A constrained exact representation at one prescribed component count. -/
structure SaturationWitness
    (r : ℚ) (c : PhysicalConstraint) (k : ℕ) where
  support : Support
  admissible : support.Admissible smallBlockSizes c
  value_eq : support.value = r
  grade_eq : support.grade = k

/-- The grade spectrum at `r` contains a principal final ideal. -/
def CofiniteSaturation (r : ℚ) (c : PhysicalConstraint) : Prop :=
  ∃ N : ℕ, ∀ k, N ≤ k → Nonempty (SaturationWitness r c k)

/--
Application-facing form of interval saturation: once each local grade interval
has literal witnesses, overlap and cofinality give the final ideal.
-/
theorem cofiniteSaturation_of_interval_witnesses
    (r : ℚ) (c : PhysicalConstraint)
    (lower upper : ℕ → ℕ)
    (hoverlap : ∀ n, lower (n + 1) ≤ upper n + 1)
    (hcofinal : ∀ k, ∃ n, k ≤ upper n)
    (hrealize : ∀ n k, lower n ≤ k → k ≤ upper n →
      Nonempty (SaturationWitness r c k)) :
    CofiniteSaturation r c := by
  refine ⟨lower 0, fun k hk => ?_⟩
  rcases AffineCorrection.mem_intervalSpectrum_of_ge
      lower upper hoverlap hcofinal hk with ⟨n, hlow, hupp⟩
  exact hrealize n k hlow hupp

/-- Number of ternary connected components of a finite support. -/
noncomputable def Support.ternaryGrade (S : Support) : ℕ :=
  Nat.card {b : S.Blocks // S.blockSize b = 3}

/-- The ternary part is bounded independently of the eventual grade. -/
def BoundedTernarySaturation (r : ℚ) (c : PhysicalConstraint) : Prop :=
  ∃ B N : ℕ, ∀ k, N ≤ k →
    ∃ w : SaturationWitness r c k, w.support.ternaryGrade ≤ B

/-- Maximal positive-rational theorem exposed by the current architecture. -/
def PositiveRationalSaturationStatement : Prop :=
  ∀ r : ℚ, 0 < r → ∀ c : PhysicalConstraint,
    CofiniteSaturation r c ∧ BoundedTernarySaturation r c

/-- The original Erdős 289 constraint. -/
def originalConstraint : PhysicalConstraint where
  obstacle := ∅
  separation := 1

/-- Erdős 289: the exact reciprocal grade spectrum at `1` is cofinite. -/
def Erdos289Statement : Prop :=
  CofiniteSaturation 1 originalConstraint

theorem erdos289_of_positiveRationalSaturation
    (h : PositiveRationalSaturationStatement) : Erdos289Statement := by
  exact (h 1 (by norm_num) originalConstraint).1

end Erdos289
