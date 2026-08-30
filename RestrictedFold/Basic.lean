import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Data.Finset.Powerset

/-!
# Restricted additive fold

The carrier of leaf RF: for a finite subobject `A` of an additive object, the
fixed-cardinality subobjects `FinSub h A` and the additive fold that sums such a
subobject.  The fold and the cardinality of its image are equivariant under
additive, hence under linear, isomorphisms.
-/

namespace Erdos289

universe u v

/-- The fixed-cardinality subobjects of a finite subobject. -/
def FinSub {S : Type u} (h : ℕ) (A : Finset S) : Finset (Finset S) :=
  A.powersetCard h

@[simp]
theorem mem_finSub {S : Type u} {h : ℕ} {A T : Finset S} :
    T ∈ FinSub h A ↔ T ⊆ A ∧ T.card = h :=
  Finset.mem_powersetCard

theorem finSub_nonempty {S : Type u} {h : ℕ} {A : Finset S} (hh : h ≤ A.card) :
    (FinSub h A).Nonempty :=
  Finset.powersetCard_nonempty.2 hh

/-- The additive fold of a finite subobject. -/
def restrictedFold {S : Type u} [AddCommMonoid S] (T : Finset S) : S := ∑ x ∈ T, x

/-- The image of the additive fold on the fixed-cardinality subobjects of `A`. -/
def restrictedFoldImage {S : Type u} [AddCommMonoid S] [DecidableEq S]
    (h : ℕ) (A : Finset S) : Finset S :=
  (FinSub h A).image restrictedFold

theorem mem_restrictedFoldImage {S : Type u} [AddCommMonoid S] [DecidableEq S]
    {h : ℕ} {A : Finset S} {y : S} :
    y ∈ restrictedFoldImage h A ↔ ∃ T ⊆ A, T.card = h ∧ restrictedFold T = y := by
  simp only [restrictedFoldImage, Finset.mem_image, mem_finSub]
  constructor
  · rintro ⟨T, ⟨hsub, hcard⟩, hy⟩
    exact ⟨T, hsub, hcard, hy⟩
  · rintro ⟨T, hsub, hcard, hy⟩
    exact ⟨T, ⟨hsub, hcard⟩, hy⟩

theorem restrictedFoldImage_nonempty {S : Type u} [AddCommMonoid S] [DecidableEq S]
    {h : ℕ} {A : Finset S} (hh : h ≤ A.card) : (restrictedFoldImage h A).Nonempty :=
  (finSub_nonempty hh).image _

/-! ## Equivariance under additive and linear isomorphisms -/

section Transport

variable {S : Type u} {S' : Type v} [AddCommMonoid S] [AddCommMonoid S']

/-- The fold is equivariant under an additive isomorphism. -/
theorem restrictedFold_map (e : S ≃+ S') (T : Finset S) :
    restrictedFold (T.map e.toEquiv.toEmbedding) = e (restrictedFold T) := by
  rw [restrictedFold, restrictedFold, Finset.sum_map, map_sum]
  rfl

/-- Fixed-cardinality subobjects are transported by an additive isomorphism. -/
theorem finSub_map (e : S ≃+ S') (h : ℕ) (A : Finset S) :
    FinSub h (A.map e.toEquiv.toEmbedding) =
      (FinSub h A).map (Finset.mapEmbedding e.toEquiv.toEmbedding).toEmbedding :=
  Finset.powersetCard_map _ _ _

/-- The fold image is transported by an additive isomorphism. -/
theorem restrictedFoldImage_map [DecidableEq S] [DecidableEq S']
    (e : S ≃+ S') (h : ℕ) (A : Finset S) :
    restrictedFoldImage h (A.map e.toEquiv.toEmbedding) =
      (restrictedFoldImage h A).map e.toEquiv.toEmbedding := by
  classical
  rw [restrictedFoldImage, finSub_map, Finset.map_eq_image, Finset.image_image,
    restrictedFoldImage, Finset.map_eq_image, Finset.image_image]
  refine Finset.image_congr fun T _ ↦ ?_
  simpa using restrictedFold_map e T

/-- The fold image cardinality is invariant under an additive isomorphism. -/
theorem card_restrictedFoldImage_map [DecidableEq S] [DecidableEq S']
    (e : S ≃+ S') (h : ℕ) (A : Finset S) :
    (restrictedFoldImage h (A.map e.toEquiv.toEmbedding)).card =
      (restrictedFoldImage h A).card := by
  rw [restrictedFoldImage_map, Finset.card_map]

/-- The fold image cardinality is invariant under a linear isomorphism; this is
the equivariance consumed by the basis-free descent of leaf RF. -/
theorem card_restrictedFoldImage_linearEquiv {R : Type*} [Semiring R]
    [Module R S] [Module R S'] [DecidableEq S] [DecidableEq S']
    (e : S ≃ₗ[R] S') (h : ℕ) (A : Finset S) :
    (restrictedFoldImage h (A.map e.toAddEquiv.toEquiv.toEmbedding)).card =
      (restrictedFoldImage h A).card :=
  card_restrictedFoldImage_map e.toAddEquiv h A

end Transport

end Erdos289
