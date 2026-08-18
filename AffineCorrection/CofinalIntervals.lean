module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Set.Defs

@[expose] public section

/-!
# Cofinal saturation by overlapping integer intervals

This is the order-theoretic endpoint of the enriched saturation engine.  A
sequence of attainable closed grade intervals whose consecutive members meet
or touch, and whose upper endpoints are cofinal, contains a principal final
ideal.  No quantitative coordinates used to prove the hypotheses occur in the
conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AffineCorrection

/-- Grades covered by at least one interval `[lower n, upper n]`. -/
def intervalSpectrum (lower upper : ℕ → ℕ) : Set ℕ :=
  {k | ∃ n, lower n ≤ k ∧ k ≤ upper n}

/--
Touching consecutive intervals with cofinal upper endpoints cover every grade
above the first lower endpoint.
-/
theorem mem_intervalSpectrum_of_ge
    (lower upper : ℕ → ℕ)
    (hoverlap : ∀ n, lower (n + 1) ≤ upper n + 1)
    (hcofinal : ∀ k, ∃ n, k ≤ upper n)
    {k : ℕ} (hk : lower 0 ≤ k) :
    k ∈ intervalSpectrum lower upper := by
  let n := Nat.find (hcofinal k)
  have hn : n = Nat.find (hcofinal k) := rfl
  have hkn : k ≤ upper n := Nat.find_spec (hcofinal k)
  refine ⟨n, ?_, hkn⟩
  rcases n with _ | n
  · exact hk
  · have hminimal : ¬k ≤ upper n := by
      intro h
      have hle := Nat.find_min' (hcofinal k) h
      omega
    exact le_trans (hoverlap n) (by omega)

/-- The interval spectrum contains the principal final ideal at `lower 0`. -/
theorem Ici_subset_intervalSpectrum
    (lower upper : ℕ → ℕ)
    (hoverlap : ∀ n, lower (n + 1) ≤ upper n + 1)
    (hcofinal : ∀ k, ∃ n, k ≤ upper n) :
    Set.Ici (lower 0) ⊆ intervalSpectrum lower upper := by
  intro k hk
  exact mem_intervalSpectrum_of_ge lower upper hoverlap hcofinal hk

/-- Cofiniteness in the existential form consumed by the E289 statement. -/
theorem intervalSpectrum_cofinite
    (lower upper : ℕ → ℕ)
    (hoverlap : ∀ n, lower (n + 1) ≤ upper n + 1)
    (hcofinal : ∀ k, ∃ n, k ≤ upper n) :
    ∃ N, ∀ k, N ≤ k → k ∈ intervalSpectrum lower upper := by
  exact ⟨lower 0, fun _ hk =>
    mem_intervalSpectrum_of_ge lower upper hoverlap hcofinal hk⟩

/--
The manuscript's form of the eventual-ray criterion: overlap is only required
from some stage on, and cofinality of the right endpoints is asked for from
that stage on as well — which is what `B_j → ∞` supplies.  No hypothesis on the
left endpoints is needed.
-/
theorem intervalSpectrum_cofinite_of_eventually
    (lower upper : ℕ → ℕ) (n₀ : ℕ)
    (hoverlap : ∀ n, n₀ ≤ n → lower (n + 1) ≤ upper n + 1)
    (hcofinal : ∀ k, ∃ n, n₀ ≤ n ∧ k ≤ upper n) :
    ∃ N, ∀ k, N ≤ k → k ∈ intervalSpectrum lower upper := by
  refine ⟨lower n₀, fun k hk => ?_⟩
  have hshift :=
    mem_intervalSpectrum_of_ge (fun n => lower (n₀ + n)) (fun n => upper (n₀ + n))
      (fun n => hoverlap (n₀ + n) (Nat.le_add_right _ _))
      (fun k => by
        obtain ⟨n, hn, hkn⟩ := hcofinal k
        exact ⟨n - n₀, by rwa [Nat.add_sub_cancel' hn]⟩)
      (k := k) (by simpa using hk)
  obtain ⟨m, hlow, hupp⟩ := hshift
  exact ⟨n₀ + m, hlow, hupp⟩

end AffineCorrection
