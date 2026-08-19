module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PathSupport

@[expose] public section

/-!
# Constrained presentation and deformation fibres

These declarations name the constrained fibres of the reciprocal fold: the
presentations of a prescribed value, and the deformations realizing a
prescribed pair of increments in value and grade.  They contain no splitting
algorithm and no polynomial coordinates; concrete formulas belong only in the
proofs that construct points of these objects.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- All distinct denominator vertices in a support are farther apart than a margin. -/
def Support.PointSeparated (S : Support) (margin : ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → margin < Nat.dist a.1 b.1

/-- The intrinsic constrained fibre of the reciprocal fold over a rational value. -/
structure RationalPresentation
    (q : ℚ) (c : PhysicalConstraint) where
  support : Support
  value_eq : support.value = q
  avoids : support.Avoids c
  pointSeparated : support.PointSeparated c.separation

/-- A remote, coefficient-one presentation of one unit fraction. -/
structure UnitFractionPresentation
    (n : Denominator) (c : PhysicalConstraint) where
  support : Support
  value_eq : support.value = reciprocal n
  avoids : support.Avoids c
  pointSeparated : support.PointSeparated c.separation

/-- Forget that the target was presented syntactically as a unit fraction. -/
def UnitFractionPresentation.toRational
    {n : Denominator} {c : PhysicalConstraint}
    (w : UnitFractionPresentation n c) :
    RationalPresentation (reciprocal n) c where
  support := w.support
  value_eq := w.value_eq
  avoids := w.avoids
  pointSeparated := w.pointSeparated

/-- Every constrained unit-fraction presentation fibre is inhabited. -/
def UnitFractionRefinementCofinality : Prop :=
  ∀ (n : Denominator) (c : PhysicalConstraint),
    Nonempty (UnitFractionPresentation n c)

/-- The canonical same-grade exact-difference fibre used by mobility. -/
structure SameGradeDeformation
    (q : ℚ) (c : PhysicalConstraint) where
  lower : Support
  upper : Support
  lower_admissible : lower.Admissible smallBlockSizes c
  upper_admissible : upper.Admissible smallBlockSizes c
  value_eq : upper.value = lower.value + q
  grade_eq : upper.grade = lower.grade

/-- The same-grade deformation fibre cut out by a lower-state resource bound. -/
structure LightMobilityPoint
    (q : ℚ) (c : PhysicalConstraint) (ε : ℚ)
    extends SameGradeDeformation q c where
  lower_value_lt : lower.value < ε

/-- Arbitrarily-light mobility for every positive rational increment. -/
def ArbitrarilyLightMobility : Prop :=
  ∀ (q : ℚ), 0 < q → ∀ (c : PhysicalConstraint) (ε : ℚ), 0 < ε →
    Nonempty (LightMobilityPoint q c ε)

/-- A block-supported approximation from above, with its exact component cost. -/
structure PositiveExcessBlockification
    (q : ℚ) (c : PhysicalConstraint) (ε : ℚ) where
  support : Support
  excess : ℚ
  atoms : ℕ
  admissible : support.Admissible smallBlockSizes c
  value_eq : support.value = q + excess
  grade_eq : support.grade = atoms
  excess_pos : 0 < excess
  excess_lt : excess < ε

/-- The canonical `(ΔW, Δg) = (0,1)` fibre with a resource bound. -/
structure NeutralGradeOnePoint
    (c : PhysicalConstraint) (ε : ℚ) where
  lower : Support
  upper : Support
  lower_admissible : lower.Admissible smallBlockSizes c
  upper_admissible : upper.Admissible smallBlockSizes c
  value_eq : upper.value = lower.value
  grade_eq : upper.grade = lower.grade + 1
  value_pos : 0 < lower.value
  value_lt : lower.value < ε

/-- A light neutral deformation with an arbitrary exact grade increment. -/
structure NeutralGradePoint
    (k : ℕ) (c : PhysicalConstraint) (ε : ℚ) where
  lower : Support
  upper : Support
  lower_admissible : lower.Admissible smallBlockSizes c
  upper_admissible : upper.Admissible smallBlockSizes c
  value_eq : upper.value = lower.value
  grade_eq : upper.grade = lower.grade + k
  lower_value_lt : lower.value < ε

/-- The neutral grade-one fibre has arbitrarily light remote points. -/
def RemoteLightNeutralGradeOne : Prop :=
  ∀ (c : PhysicalConstraint) (ε : ℚ), 0 < ε →
    Nonempty (NeutralGradeOnePoint c ε)

end Erdos289
