module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.LocalProfiles

@[expose] public section

/-!
# The epimorphic grade interval of a prime row

`Erdos289.TransverseReservoir.restrictedFold_coversAtGrade` covers one grade at
a time, under the Dias da Silva–Hamidoune condition `p ≤ h (m - h) + 1` on the
row size `m`.  The descent needs the *interval* of grades so covered, because
the aggregation step decomposes a target grade as a sum of one contribution per
stage.

The interval is intrinsic and needs no choice: `h ↦ h (m - h)` is concave, so
the condition holds on all of `[a, m - a]` as soon as it holds at the endpoint
`a`.  That concavity is the only new content here, and it is the elementary
identity `(h - a) (t - a) ≥ 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/--
Concavity of `h ↦ h (m - h)` in the only form needed: the product is
minimised at the ends of the symmetric range `[a, m - a]`.
-/
theorem mul_sub_le_mul_sub_of_between {a h m : ℕ} (hah : a ≤ h) (hhm : h + a ≤ m) :
    a * (m - a) ≤ h * (m - h) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = h + t := ⟨m - h, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, h = a + u := ⟨h - a, by omega⟩
  have hat : a ≤ t := by omega
  have h1 : a + u + t - a = u + t := by omega
  have h2 : a + u + t - (a + u) = t := by omega
  rw [h1, h2]
  calc a * (u + t) = a * u + a * t := Nat.mul_add a u t
    _ ≤ t * u + a * t := Nat.add_le_add_right (Nat.mul_le_mul hat (Nat.le_refl u)) _
    _ = a * t + u * t := by rw [Nat.mul_comm t u, Nat.add_comm]
    _ = (a + u) * t := (Nat.add_mul a u t).symm

namespace TransverseReservoir

/--
Leaf `D` in the form the aggregation consumes: a prime row of size `m` is
epimorphic at *every* grade of the symmetric interval `[a, m - a]`, as soon as
the restricted-fold condition holds at its lower endpoint `a`.
-/
theorem restrictedFold_coversAtGrade_of_mem_Icc
    {Q p e : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (hne : R.simpleValues.Nonempty) {a h : ℕ}
    (hah : a ≤ h) (hhm : h + a ≤ R.simpleValues.card)
    (hend : p ≤ a * (R.simpleValues.card - a) + 1) :
    CoversAtGrade (RestrictedFold.fold R.simpleValues h) (fun _ ↦ h) h := by
  refine restrictedFold_coversAtGrade R hp he hQ hne (by omega) ?_
  have := mul_sub_le_mul_sub_of_between hah hhm
  omega

/--
The same statement as a property of the whole grade interval.  This is the
object the interval-aggregation step of the descent sums over.
-/
theorem restrictedFold_coversAtGrade_Icc
    {Q p e : ℕ} {c : PhysicalConstraint}
    (R : TransverseReservoir Q c) (hp : p.Prime) (he : 0 < e) (hQ : Q = p ^ e)
    (hne : R.simpleValues.Nonempty) {a : ℕ}
    (hend : p ≤ a * (R.simpleValues.card - a) + 1) :
    ∀ h ∈ Finset.Icc a (R.simpleValues.card - a),
      CoversAtGrade (RestrictedFold.fold R.simpleValues h) (fun _ ↦ h) h := by
  intro h hh
  rcases Finset.mem_Icc.mp hh with ⟨h1, h2⟩
  exact restrictedFold_coversAtGrade_of_mem_Icc R hp he hQ hne h1 (by omega) hend

end TransverseReservoir

end Erdos289
