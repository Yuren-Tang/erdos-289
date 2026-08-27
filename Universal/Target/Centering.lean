import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Marked-family centering

The cokernel of the free abelian map induced by an arbitrary family of marks.
-/

open CategoryTheory
open QuotientAddGroup

namespace Erdos289

universe u

/-- The category of set-valued markings of an abelian group `Γ`, namely
`Type / Γ`. -/
abbrev Marking (Γ : Type u) := CategoryTheory.Over (X := Γ)

/-- The homomorphism from the free abelian group on the marks induced by a
marking. -/
def markingFreeMap {Γ : Type u} [AddCommGroup Γ] (t : Marking Γ) :
    FreeAbelianGroup t.left →+ Γ :=
  FreeAbelianGroup.lift t.hom

/-- The centered target: the cokernel of the free abelian map induced by the
marking. -/
abbrev CenteredMarking {Γ : Type u} [AddCommGroup Γ] (t : Marking Γ) :=
  Γ ⧸ (markingFreeMap t).range

/-- The canonical quotient map to the centered target. -/
def markingQuotient {Γ : Type u} [AddCommGroup Γ] (t : Marking Γ) :
    Γ →+ CenteredMarking t :=
  QuotientAddGroup.mk' (markingFreeMap t).range

private theorem markingFreeMap_comp {Γ : Type u} [AddCommGroup Γ]
    {t t' : Marking Γ} (h : t ⟶ t') :
    (markingFreeMap t').comp (FreeAbelianGroup.map fun a ↦ h.left a) =
      markingFreeMap t := by
  apply FreeAbelianGroup.lift_ext
  intro a
  simp only [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply,
    markingFreeMap, FreeAbelianGroup.lift_apply_of]
  exact CategoryTheory.congr_fun (Over.w h) a

private theorem markingRange_le {Γ : Type u} [AddCommGroup Γ]
    {t t' : Marking Γ} (h : t ⟶ t') :
    (markingFreeMap t).range ≤ (markingFreeMap t').range := by
  rintro z ⟨w, rfl⟩
  refine ⟨FreeAbelianGroup.map (fun a ↦ h.left a) w, ?_⟩
  exact DFunLike.congr_fun (markingFreeMap_comp h) w

/-- The comparison of centered targets induced by a morphism of markings. -/
def markingCenteringMap {Γ : Type u} [AddCommGroup Γ]
    {t t' : Marking Γ} (h : t ⟶ t') : CenteredMarking t →+ CenteredMarking t' :=
  QuotientAddGroup.map (markingFreeMap t).range (markingFreeMap t').range
    (AddMonoidHom.id Γ) (by simpa using markingRange_le h)

@[simp]
theorem markingCenteringMap_quotient {Γ : Type u} [AddCommGroup Γ]
    {t t' : Marking Γ} (h : t ⟶ t') (x : Γ) :
    markingCenteringMap h (markingQuotient t x) = markingQuotient t' x :=
  rfl

/-- Centering is functorial in the marking. -/
def markingCentering_functorial (Γ : Type u) [AddCommGroup Γ] :
    Marking Γ ⥤ AddCommGrpCat.{u} where
  obj t := AddCommGrpCat.of (CenteredMarking t)
  map h := AddCommGrpCat.ofHom (markingCenteringMap h)
  map_id t := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (markingFreeMap t).range z
    rfl
  map_comp h k := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (markingFreeMap _).range z
    rfl

/-- The quotient universal property: additive observations out of `Γ` factor
uniquely through the centered target exactly when they kill every mark. -/
theorem markingCentering_isInitial {Γ B : Type u} [AddCommGroup Γ] [AddCommGroup B]
    (t : Marking Γ) (f : Γ →+ B) :
    (∀ a : t.left, f (t.hom a) = 0) ↔
      ∃! fbar : CenteredMarking t →+ B, fbar.comp (markingQuotient t) = f := by
  constructor
  · intro hkill
    have hrange : (markingFreeMap t).range ≤ f.ker := by
      rintro _ ⟨w, rfl⟩
      have hzero : f.comp (markingFreeMap t) = 0 := by
        apply FreeAbelianGroup.lift_ext
        intro a
        simp [markingFreeMap, hkill a]
      exact DFunLike.congr_fun hzero w
    let fbar : CenteredMarking t →+ B :=
      QuotientAddGroup.lift (markingFreeMap t).range f hrange
    refine ⟨fbar, ?_, ?_⟩
    · exact QuotientAddGroup.lift_comp_mk' (markingFreeMap t).range f hrange
    · intro g hg
      apply AddMonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (markingFreeMap t).range z
      exact DFunLike.congr_fun hg x
  · rintro ⟨fbar, hfac, _⟩ a
    have hmem : t.hom a ∈ (markingFreeMap t).range := by
      refine ⟨FreeAbelianGroup.of a, ?_⟩
      simp [markingFreeMap]
    have hqzero : markingQuotient t (t.hom a) = 0 := by
      exact (eq_zero_iff _).mpr hmem
    calc
      f (t.hom a) = fbar (markingQuotient t (t.hom a)) := by
        rw [← hfac]
        rfl
      _ = fbar 0 := congrArg fbar hqzero
      _ = 0 := fbar.map_zero

/-- The canonical one-point marking at `τ`. -/
def singletonMarking {Γ : Type u} (τ : Γ) : Marking Γ :=
  Over.mk (TypeCat.ofHom fun _ : PUnit ↦ τ)

end Erdos289
