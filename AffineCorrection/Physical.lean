module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Defs

@[expose] public section

/-!
# Partial physical resources

The physical system is presented by the graph of a partial commutative
addition.  This is the Set-level normal form of a multiplication-domain
subobject together with its multiplication map.

No family homogeneity or all-pairs compatibility notion is primitive here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AffineCorrection

universe u v w

/--
A relation presentation of a partial commutative monoid.

`add a b c` means that the physical resources `a` and `b` are compatible and
have composite `c`.
-/
structure PartialAddCommMonoid (C : Type u) where
  /-- Empty physical resource. -/
  zero : C
  /-- Graph of the partial multiplication. -/
  add : C → C → C → Prop
  /-- The partial multiplication is single-valued. -/
  functional :
    ∀ {a b c c' : C}, add a b c → add a b c' → c = c'
  /-- Empty resource is a left unit. -/
  zero_add : ∀ a : C, add zero a a
  /-- Defined physical multiplication is commutative. -/
  add_comm :
    ∀ {a b c : C}, add a b c → add b a c
  /-- Relational associativity of the partial multiplication. -/
  add_assoc :
    ∀ a b c w : C,
      (∃ ab, add a b ab ∧ add ab c w) ↔
      (∃ bc, add b c bc ∧ add a bc w)

namespace PartialAddCommMonoid

variable {C : Type u} (P : PartialAddCommMonoid C)

/-- Two physical states are compatible iff their partial sum exists. -/
def Compatible (a b : C) : Prop :=
  ∃ c, P.add a b c

/--
The image family consisting of actual defined sums of one state from `F` and
one state from `R`.
-/
def sumFamily (F R : Set C) : Set C :=
  {z | ∃ x, x ∈ F ∧ ∃ y, y ∈ R ∧ P.add x y z}

end PartialAddCommMonoid

/-- A function is additive on every defined physical sum. -/
def IsAdditiveOn
    {C : Type u} {A : Type v} [Add A]
    (P : PartialAddCommMonoid C) (f : C → A) : Prop :=
  ∀ {a b c : C}, P.add a b c → f c = f a + f b

/-- Grade spectrum of the exact fibre at `τ`. -/
def exactSpectrum
    {C : Type u} {Γ : Type v} {M : Type w}
    (W : C → Γ) (g : C → M) (τ : Γ) : Set M :=
  {m | ∃ x, W x = τ ∧ g x = m}

end AffineCorrection
