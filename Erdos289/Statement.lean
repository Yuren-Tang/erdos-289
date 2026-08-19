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

/--
A constrained exact representation at one prescribed component count, inside a
prescribed class of block sizes.
-/
structure SaturationWitness
    (L : Set ℕ) (r : ℚ) (c : PhysicalConstraint) (k : ℕ) where
  support : Support
  admissible : support.Admissible L c
  value_eq : support.value = r
  grade_eq : support.grade = k

/-- Enlarging the class of admitted block sizes weakens a witness. -/
def SaturationWitness.mono {L L' : Set ℕ} (h : L ⊆ L')
    {r : ℚ} {c : PhysicalConstraint} {k : ℕ} (w : SaturationWitness L r c k) :
    SaturationWitness L' r c k where
  support := w.support
  admissible := ⟨fun b => h (w.admissible.1 b), w.admissible.2.1, w.admissible.2.2⟩
  value_eq := w.value_eq
  grade_eq := w.grade_eq

/-- The grade spectrum at `r` contains a principal final ideal. -/
def CofiniteSaturation (L : Set ℕ) (r : ℚ) (c : PhysicalConstraint) : Prop :=
  ∃ N : ℕ, ∀ k, N ≤ k → Nonempty (SaturationWitness L r c k)

theorem CofiniteSaturation.mono {L L' : Set ℕ} (h : L ⊆ L')
    {r : ℚ} {c : PhysicalConstraint} (hs : CofiniteSaturation L r c) :
    CofiniteSaturation L' r c := by
  obtain ⟨N, hN⟩ := hs
  exact ⟨N, fun k hk => (hN k hk).map (SaturationWitness.mono h)⟩

/--
Application-facing form of interval saturation: once each local grade interval
has literal witnesses, overlap and cofinality give the final ideal.
-/
theorem cofiniteSaturation_of_interval_witnesses
    (L : Set ℕ) (r : ℚ) (c : PhysicalConstraint)
    (lower upper : ℕ → ℕ)
    (hoverlap : ∀ n, lower (n + 1) ≤ upper n + 1)
    (hcofinal : ∀ k, ∃ n, k ≤ upper n)
    (hrealize : ∀ n k, lower n ≤ k → k ≤ upper n →
      Nonempty (SaturationWitness L r c k)) :
    CofiniteSaturation L r c := by
  refine ⟨lower 0, fun k hk => ?_⟩
  rcases AffineCorrection.mem_intervalSpectrum_of_ge
      lower upper hoverlap hcofinal hk with ⟨n, hlow, hupp⟩
  exact hrealize n k hlow hupp

/-- Number of ternary connected components of a finite support. -/
noncomputable def Support.ternaryGrade (S : Support) : ℕ :=
  Nat.card {b : S.Blocks // S.blockSize b = 3}

/-- The ternary part is bounded independently of the eventual grade. -/
def BoundedTernarySaturation (L : Set ℕ) (r : ℚ) (c : PhysicalConstraint) : Prop :=
  ∃ B N : ℕ, ∀ k, N ≤ k →
    ∃ w : SaturationWitness L r c k, w.support.ternaryGrade ≤ B

/-- Maximal positive-rational theorem exposed by the current architecture. -/
def PositiveRationalSaturation (L : Set ℕ) : Prop :=
  ∀ r : ℚ, 0 < r → ∀ c : PhysicalConstraint,
    CofiniteSaturation L r c ∧ BoundedTernarySaturation L r c

/--
The physical constraint of the source problem: no forbidden denominators, and
distinct blocks separated by more than one, that is, non-adjacent.
-/
def originalConstraint : PhysicalConstraint where
  obstacle := ∅
  separation := 1

/--
The intrinsic form of the source problem: the exact reciprocal grade spectrum
at `1` is cofinite, over the problem's own class of block sizes — every block of
length at least two.
-/
def IntervalSaturation : Prop :=
  CofiniteSaturation nontrivialBlockSizes 1 originalConstraint

/--
The strengthening this development proves: the same statement with every block
of length exactly two or three.
-/
def SmallBlockSaturation : Prop :=
  CofiniteSaturation smallBlockSizes 1 originalConstraint

theorem intervalSaturation_of_smallBlock (h : SmallBlockSaturation) :
    IntervalSaturation :=
  CofiniteSaturation.mono smallBlockSizes_subset_nontrivial h

theorem intervalSaturation_of_positiveRational
    (h : PositiveRationalSaturation nontrivialBlockSizes) : IntervalSaturation :=
  (h 1 (by norm_num) originalConstraint).1

end Erdos289
