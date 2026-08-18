module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection.GradeResource
public import Mathlib.Combinatorics.Quiver.Path

@[expose] public section

/-!
# Free grade-resource enriched closure

A weighted quiver freely generates a category enriched in the grade-resource
quantale.  The hom-profile is the join of the weights of all directed paths.
The final theorem is its universal property: it is the least reflexive,
transitive profile system containing the generating edge weights.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AffineCorrection

open Quiver

universe u v w t

namespace FreeClosure

variable
    {X : Type u} [Quiver.{v} X]
    {M : Type w} {B : Type t}
    [AddCommMonoid M] [AddCommMonoid B]

/-- Multiplicative weight of a path in a grade-resource weighted quiver. -/
def pathWeight
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    {x y : X} (p : Path x y) : GradeResource M B :=
  p.recOn 1 (fun _ e weight => weight * edgeWeight e)

@[simp]
theorem pathWeight_nil
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B) (x : X) :
    pathWeight edgeWeight (.nil : Path x x) = 1 := by
  rfl

@[simp]
theorem pathWeight_cons
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    {x y z : X} (p : Path x y) (e : y ⟶ z) :
    pathWeight edgeWeight (p.cons e) = pathWeight edgeWeight p * edgeWeight e := by
  rfl

theorem pathWeight_comp
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    {x y z : X} (p : Path x y) (q : Path y z) :
    pathWeight edgeWeight (p.comp q) =
      pathWeight edgeWeight p * pathWeight edgeWeight q := by
  induction q with
  | nil => simp
  | cons q e ih => simp [ih, mul_assoc]

/-- The free enriched hom-profile: the join of the weights of all paths. -/
def hom
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    (x y : X) : GradeResource M B :=
  ⨆ p : Path x y, pathWeight edgeWeight p

theorem edge_le_hom
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    {x y : X} (e : x ⟶ y) :
    edgeWeight e ≤ hom edgeWeight x y := by
  have hpath : pathWeight edgeWeight e.toPath = edgeWeight e := by simp [Hom.toPath]
  rw [← hpath]
  exact le_iSup (fun p : Path x y => pathWeight edgeWeight p) e.toPath

theorem one_le_hom
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    (x : X) : 1 ≤ hom edgeWeight x x := by
  rw [← pathWeight_nil edgeWeight x]
  exact le_iSup (fun p : Path x x => pathWeight edgeWeight p) .nil

theorem mul_hom_le_hom
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    (x y z : X) :
    hom edgeWeight x y * hom edgeWeight y z ≤ hom edgeWeight x z := by
  unfold hom
  rw [Quantale.iSup_mul_distrib]
  refine iSup_le fun p => ?_
  rw [Quantale.mul_iSup_distrib]
  refine iSup_le fun q => ?_
  rw [← pathWeight_comp edgeWeight p q]
  exact le_iSup (fun r : Path x z => pathWeight edgeWeight r) (p.comp q)

/-- A reflexive and transitive grade-resource enrichment on the vertices. -/
structure Enrichment (X : Type u) (M : Type w) (B : Type t)
    [AddCommMonoid M] [AddCommMonoid B] where
  hom : X → X → GradeResource M B
  refl : ∀ x, 1 ≤ hom x x
  comp : ∀ x y z, hom x y * hom y z ≤ hom x z

/-- Universal property of the free enriched closure. -/
theorem hom_le_of_edge_le
    (edgeWeight : ∀ {x y : X}, (x ⟶ y) → GradeResource M B)
    (R : Enrichment X M B)
    (hedge : ∀ {x y : X} (e : x ⟶ y), edgeWeight e ≤ R.hom x y)
    (x y : X) : hom edgeWeight x y ≤ R.hom x y := by
  unfold hom
  refine iSup_le fun p => ?_
  induction p with
  | nil =>
      simpa using R.refl x
  | @cons y z p e ih =>
      apply le_trans _ (R.comp x y z)
      exact le_trans (mul_le_mul_left ih (edgeWeight e))
        (mul_le_mul_right (hedge e) (R.hom x y))

end FreeClosure

end AffineCorrection
