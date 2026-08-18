module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.ZMod.Basic
import LeanPool.PolynomialMethodRestrictedSums.DiasDaSilvaHamidoune

@[expose] public section

/-!
# Fixed-cardinality additive folds

The restricted sumset leaf is exposed as surjectivity of the canonical fold
from the object of `h`-element subobjects.  No coordinate choice or name of a
proof theorem occurs in the interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

universe u

namespace RestrictedFold

variable {G : Type u} [AddCommMonoid G]

/-- The finite-subset object of fixed cardinality inside `A`. -/
def Domain (A : Finset G) (h : ℕ) :=
  {S : Finset G // S ⊆ A ∧ S.card = h}

/-- Canonical additive fold on a fixed-cardinality subset. -/
def fold (A : Finset G) (h : ℕ) : Domain A h → G :=
  fun S => ∑ x ∈ S.1, x

/-- The finite image of the canonical fixed-cardinality fold. -/
def image [DecidableEq G] (A : Finset G) (h : ℕ) : Finset G :=
  (A.powersetCard h).image fun S => ∑ x ∈ S, x

/-- The intrinsic restricted-sumset assertion consumed downstream. -/
def Surjective (A : Finset G) (h : ℕ) : Prop :=
  Function.Surjective (fold A h)

theorem surjective_iff_image_eq_univ (A : Finset G) (h : ℕ) :
    Surjective A h ↔ Set.range (fold A h) = Set.univ := by
  exact Set.range_eq_univ.symm

variable [DecidableEq G]

theorem mem_image_iff (A : Finset G) (h : ℕ) (x : G) :
    x ∈ image A h ↔ ∃ S : Domain A h, fold A h S = x := by
  simp only [image, Finset.mem_image, Finset.mem_powersetCard, Domain, fold]
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact ⟨⟨S, hS⟩, rfl⟩
  · rintro ⟨⟨S, hS⟩, rfl⟩
    exact ⟨S, hS, rfl⟩

theorem surjective_iff_image_eq_univ_finset [Fintype G]
    (A : Finset G) (h : ℕ) :
    Surjective A h ↔ image A h = Finset.univ := by
  constructor
  · intro hsurj
    apply Finset.eq_univ_of_forall
    intro x
    exact (mem_image_iff A h x).2 (hsurj x)
  · intro himage x
    have hx : x ∈ image A h := by rw [himage]; simp
    exact (mem_image_iff A h x).1 hx

section ZMod

variable {p : ℕ} [Fact p.Prime]

/--
Hard leaf D (Dias da Silva--Hamidoune), phrased as image growth of the
canonical fold from the cardinality-`h` finite-subset object.
-/
theorem image_card_lower_bound
    (A : Finset (ZMod p)) (h : ℕ)
    (hA : A.Nonempty) (hh : h ≤ A.card) :
    min p (h * (A.card - h) + 1) ≤ (image A h).card := by
  have hdonor := dias_da_silva_hamidoune A h hA hh
  have himage : image A h = distinctSumSet A h := by
    unfold image distinctSumSet
    rw [Finset.powersetCard_eq_filter]
  rw [himage]
  simpa [pow_two, Nat.mul_sub_left_distrib] using hdonor

/-- The full-image range of leaf D is exactly surjectivity of the intrinsic fold. -/
theorem surjective_of_card_bound
    (A : Finset (ZMod p)) (h : ℕ)
    (hA : A.Nonempty) (hh : h ≤ A.card)
    (hfull : p ≤ h * (A.card - h) + 1) :
    Surjective A h := by
  rw [surjective_iff_image_eq_univ_finset]
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, ZMod.card]
  have hgrowth := image_card_lower_bound A h hA hh
  simpa [min_eq_left hfull] using hgrowth

end ZMod

end RestrictedFold

end Erdos289
