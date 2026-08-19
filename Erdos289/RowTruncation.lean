module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.SignedInverseAtom

@[expose] public section

/-!
# Selecting a row: deduplication and rank truncation

Two selections turn the raw carrier band into a row certificate, and both are
pure pigeonhole.

*Deduplication.*  Carriers sharing a current coefficient come in fibres of at
most four points, so a subfamily on which the coefficient is injective retains
at least a quarter of the band.

*Rank truncation.*  Distinct coefficients are distinct naturals, so at most `t`
of them can lie below `t`: retaining the coefficients at least `t` costs at
most `t` members, for *every* threshold `t`.  The centre and mass bounds are
then exact consequences of the inverse equation, in the free parameter `t`.

Nothing here is chosen.  Both the fibre bound and the threshold are parameters;
the fact that a particular value of either is convenient downstream is a fact
about the construction, not about the row.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-! ### Deduplication -/

/--
A map with fibres of at most `d` points admits a section over its whole image:
some subfamily on which the map is injective already carries the full image, and
therefore at least a `d`-th of the domain.
-/
theorem exists_injOn_subset {α : Type*} [DecidableEq α] {β : Type*} [DecidableEq β]
    (A : Finset α) (f : α → β) {d : ℕ}
    (hfib : ∀ y ∈ A.image f, (A.filter fun x => f x = y).card ≤ d) :
    ∃ B ⊆ A, Set.InjOn f B ∧ B.image f = A.image f ∧ A.card ≤ d * B.card := by
  classical
  have hex : ∀ y : {y // y ∈ A.image f}, ∃ x, x ∈ A ∧ f x = y.1 := by
    intro y
    rcases Finset.mem_image.mp y.2 with ⟨x, hx, hfx⟩
    exact ⟨x, hx, hfx⟩
  set g : {y // y ∈ A.image f} → α := fun y => (hex y).choose with hg
  have hgA : ∀ y, g y ∈ A := fun y => (hex y).choose_spec.1
  have hgf : ∀ y, f (g y) = y.1 := fun y => (hex y).choose_spec.2
  have hginj : Function.Injective g := by
    intro y z hyz
    have : (y : β) = (z : β) := by rw [← hgf y, ← hgf z, hyz]
    exact Subtype.ext this
  refine ⟨(A.image f).attach.image g, Finset.image_subset_iff.mpr (fun y _ => hgA y), ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    rcases ha with ⟨y, -, rfl⟩
    rcases hb with ⟨z, -, rfl⟩
    rw [hgf y, hgf z] at hab
    exact congrArg g (Subtype.ext hab)
  · refine Finset.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
    · rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp ha with ⟨z, -, rfl⟩
      rw [hgf z]
      exact z.2
    · exact Finset.mem_image.mpr
        ⟨g ⟨y, hy⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), hgf ⟨y, hy⟩⟩
  · refine le_trans (Finset.card_le_mul_card_image A d hfib) ?_
    refine Nat.mul_le_mul_left d ?_
    rw [Finset.card_image_of_injective _ hginj, Finset.card_attach]

/-! ### Rank truncation -/

/--
The rank trade-off.  Discarding the elements of a finite set of naturals that
lie below a threshold `t` costs at most `t` elements, because those elements
embed into the initial segment of length `t`.
-/
theorem card_upperRank_ge (S : Finset ℕ) (t : ℕ) :
    S.card - t ≤ (S.filter fun k => t ≤ k).card := by
  classical
  have hsub : (S.filter fun k => ¬ t ≤ k) ⊆ Finset.range t := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨-, hlt⟩
    exact Finset.mem_range.mpr (by omega)
  have hle : (S.filter fun k => ¬ t ≤ k).card ≤ t := by
    refine le_trans (Finset.card_le_card hsub) ?_
    simp
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := S) (p := fun k => t ≤ k)
  omega

/--
The rank trade-off in the form the row certificate uses: on a family whose
natural-valued coefficients are pairwise distinct, retaining the coefficients
at least `t` costs at most `t` members.
-/
theorem card_upperCoefficient_ge {α : Type*}
    (B : Finset α) (f : α → ℕ) (hinj : Set.InjOn f B) (t : ℕ) :
    B.card - t ≤ (B.filter fun x => t ≤ f x).card := by
  classical
  have hcard : (B.image f).card = B.card := Finset.card_image_of_injOn hinj
  have hfilter :
      ((B.image f).filter fun k => t ≤ k)
        = (B.filter fun x => t ≤ f x).image f := Finset.filter_image
  have hinj' : Set.InjOn f (B.filter fun x => t ≤ f x) :=
    hinj.mono (by exact_mod_cast Finset.filter_subset _ _)
  have heq :
      ((B.image f).filter fun k => t ≤ k).card
        = (B.filter fun x => t ≤ f x).card := by
    rw [hfilter, Finset.card_image_of_injOn hinj']
  have hmain := card_upperRank_ge (B.image f) t
  rw [hcard] at hmain
  rw [← heq]
  exact hmain

/-- A large coefficient forces a remote distinguished centre. -/
theorem le_start_of_le_coefficient
    {Q b : ℕ} (w : ComplementaryPair Q b) (s : Orientation)
    {m : ℕ} (hm : m ≤ w.coefficient s) :
    Q * m - 1 ≤ w.start s := by
  have hmono : Q * m ≤ Q * w.coefficient s := Nat.mul_le_mul_left _ hm
  have hle := w.distinguished_le_start_succ s
  omega

/--
The exact mass bound of the row certificate: an atom whose coefficient is at
least `m` has reciprocal value below `2 / (Q m - 1)`.
-/
theorem GoodOrientation.atom_value_lt_of_le_coefficient
    {Q b p : ℕ} {w : ComplementaryPair Q b} (g : GoodOrientation p w) (hQ : 0 < Q)
    {m : ℕ} (hm : m ≤ w.coefficient g.sign) (hpos : 1 < Q * m) :
    (g.atom hQ).value < 2 / ((Q * m - 1 : ℕ) : ℚ) := by
  have hstart : Q * m - 1 ≤ w.start g.sign := le_start_of_le_coefficient w g.sign hm
  have hposQ : (0 : ℚ) < ((Q * m - 1 : ℕ) : ℚ) := by
    have : 0 < Q * m - 1 := by omega
    exact_mod_cast this
  have hcast : ((Q * m - 1 : ℕ) : ℚ) ≤ ((w.start g.sign : ℕ) : ℚ) := by
    exact_mod_cast hstart
  calc (g.atom hQ).value < 2 / ((w.start g.sign : ℕ) : ℚ) :=
        g.atom_value_lt_two_div_start hQ
    _ ≤ 2 / ((Q * m - 1 : ℕ) : ℚ) := by
        exact div_le_div_of_nonneg_left (by norm_num) hposQ hcast

end SignedInverse
end Erdos289
