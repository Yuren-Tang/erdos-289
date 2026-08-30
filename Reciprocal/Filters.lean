import Reciprocal.CurrentFiltration
import Universal.Asymptotics

import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Named current and endpoint filters

The filters through which every current, endpoint, and grade eventuality
statement of the package is expressed: the rank filter on currents, its
restriction to height-one currents, the endpoint index filter and its image
under the canonical endpoint map, and the canonical tail of currents above a
fixed rank bound.
-/

open Filter

namespace Erdos289

/-- The current filter: the rank map pulled back along `atTop`. -/
noncomputable def CurrentFilter : Filter Current := Filter.comap Current.rank Filter.atTop

/-- The height-one current filter. -/
noncomputable def HeightOneCurrentFilter : Filter Current :=
  CurrentFilter ⊓ Filter.principal {J : Current | J.height = 1}

/-- The endpoint index filter. -/
def EndpointIndexFilter : Filter ℕ := Filter.atTop

/-- The endpoint filter: the image of the endpoint index filter under the
canonical endpoint map. -/
noncomputable def EndpointFilter : Filter CompactSubgroupStage :=
  Filter.map endpoint EndpointIndexFilter

/-- The canonical tail of currents of rank at least `Q₀`. -/
abbrev CurrentTail (Q₀ : ℕ) := {J : Current // Q₀ ≤ J.rank}

/-- The canonical tail filter of `CurrentTail Q₀`. -/
noncomputable def CurrentTailFilter (Q₀ : ℕ) : Filter (CurrentTail Q₀) :=
  Filter.comap Subtype.val CurrentFilter

/-! ## Rank cofinality -/

private theorem isPrimePow_two_pow {k : ℕ} (hk : 0 < k) : IsPrimePow (2 ^ k) :=
  ⟨2, k, Nat.prime_iff.1 Nat.prime_two, hk, rfl⟩

/-- R2.7: the currents of two-power rank have unbounded rank. -/
theorem exists_current_rank_ge (N : ℕ) : ∃ J : Current, N ≤ J.rank := by
  refine ⟨currentOfPrimePow (2 ^ (N + 1)) (isPrimePow_two_pow (Nat.succ_pos N)), ?_⟩
  rw [rank_currentOfPrimePow]
  exact le_trans (Nat.le_succ N) (Nat.lt_two_pow_self).le

theorem mem_currentFilter_iff {s : Set Current} :
    s ∈ CurrentFilter ↔ ∃ N : ℕ, ∀ J : Current, N ≤ J.rank → J ∈ s := by
  constructor
  · intro hs
    obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 hs
    obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 ht
    exact ⟨N, fun J hJ ↦ hts (hN _ hJ)⟩
  · rintro ⟨N, hN⟩
    exact Filter.mem_comap.2 ⟨Set.Ici N, Filter.Ici_mem_atTop N, fun J hJ ↦ hN J hJ⟩

theorem eventually_currentFilter_iff {p : Current → Prop} :
    (∀ᶠ J in CurrentFilter, p J) ↔ ∃ N : ℕ, ∀ J : Current, N ≤ J.rank → p J :=
  mem_currentFilter_iff

instance currentFilter_neBot : CurrentFilter.NeBot := by
  rw [CurrentFilter, Filter.comap_neBot_iff]
  intro t ht
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 ht
  obtain ⟨J, hJ⟩ := exists_current_rank_ge N
  exact ⟨J, hN _ hJ⟩

/-- The rank map is cofinal for the current filter. -/
theorem tendsto_rank_atTop :
    Filter.Tendsto Current.rank CurrentFilter Filter.atTop :=
  Filter.tendsto_comap

/-! ## Endpoint cofinality -/

/-- The canonical endpoint map is cofinal for the endpoint filter. -/
theorem tendsto_endpoint : Filter.Tendsto endpoint EndpointIndexFilter EndpointFilter :=
  Filter.tendsto_map

/-- R2.5: every compact stage lies below all sufficiently large endpoints. -/
theorem eventually_le_endpoint (K : CompactSubgroupStage) :
    ∀ᶠ X in EndpointIndexFilter, K ≤ endpoint X := by
  obtain ⟨X₀, hX₀⟩ := endpoint_cofinal K
  rw [EndpointIndexFilter]
  filter_upwards [Filter.eventually_ge_atTop X₀] with X hX
  exact hX₀.trans (endpoint_mono hX)

/-! ## R2.7 — canonical current-tail filters -/

/-- R2.7: the canonical current tail is cofinal in the current filter. -/
theorem exists_currentTail_rank_ge (Q₀ N : ℕ) :
    ∃ J : CurrentTail Q₀, N ≤ J.1.rank := by
  obtain ⟨J, hJ⟩ := exists_current_rank_ge (max N Q₀)
  exact ⟨⟨J, le_trans (le_max_right N Q₀) hJ⟩, le_trans (le_max_left N Q₀) hJ⟩

instance currentTailFilter_neBot (Q₀ : ℕ) : (CurrentTailFilter Q₀).NeBot := by
  rw [CurrentTailFilter, Filter.comap_neBot_iff]
  intro t ht
  obtain ⟨N, hN⟩ := mem_currentFilter_iff.1 ht
  obtain ⟨J, hJ⟩ := exists_currentTail_rank_ge Q₀ N
  exact ⟨J, hN J.1 hJ⟩

/-- R2.7: the tail inclusion tends to the ambient current filter. -/
theorem tendsto_currentTail (Q₀ : ℕ) :
    Filter.Tendsto (Subtype.val : CurrentTail Q₀ → Current)
      (CurrentTailFilter Q₀) CurrentFilter :=
  Filter.tendsto_comap

/-- R2.7: restriction to a final rank tail is equivalent to the ambient current
filter. -/
theorem eventually_currentTailFilter_iff (Q₀ : ℕ) {p : Current → Prop} :
    (∀ᶠ J in CurrentTailFilter Q₀, p J.1) ↔ ∀ᶠ J in CurrentFilter, p J := by
  constructor
  · intro h
    obtain ⟨t, ht, hts⟩ := Filter.mem_comap.1 h
    obtain ⟨N, hN⟩ := mem_currentFilter_iff.1 ht
    refine mem_currentFilter_iff.2 ⟨max N Q₀, fun J hJ ↦ ?_⟩
    exact hts (a := ⟨J, le_trans (le_max_right N Q₀) hJ⟩)
      (hN J (le_trans (le_max_left N Q₀) hJ))
  · intro h
    exact (tendsto_currentTail Q₀).eventually h

end Erdos289
