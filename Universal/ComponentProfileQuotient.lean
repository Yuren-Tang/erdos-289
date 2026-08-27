import Universal.FiniteComponentState

import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Quotients of component profiles

The coequalizer killing an arbitrary subobject of component types is realized
canonically as the free commutative monoid on the literal complement.
-/

open CategoryTheory CategoryTheory.Limits

namespace Erdos289

universe u v

/-- The component-profile quotient killing every generator in `Θ₀`. -/
abbrev ComponentProfileQuotient {Θ : Type u} (Θ₀ : Set Θ) :=
  FCM {θ : Θ // θ ∉ Θ₀}

/-- Inclusion of the killed generators into the full free commutative monoid. -/
noncomputable def killedComponentInclusion {Θ : Type u} (Θ₀ : Set Θ) :
    FCM Θ₀ →+ FCM Θ :=
  componentLabelLift fun θ ↦ Finsupp.single θ.1 1

/-- The canonical boundary map which deletes precisely the killed generators. -/
noncomputable def componentProfileBoundary {Θ : Type u} (Θ₀ : Set Θ) :
    FCM Θ →+ ComponentProfileQuotient Θ₀ := by
  classical
  exact componentLabelLift fun θ ↦
    if h : θ ∈ Θ₀ then 0 else Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Θ₀}) 1

@[simp]
theorem componentProfileBoundary_single_of_mem {Θ : Type u} (Θ₀ : Set Θ)
    (θ : Θ) (h : θ ∈ Θ₀) :
    componentProfileBoundary Θ₀ (Finsupp.single θ 1) = 0 := by
  classical
  simp [componentProfileBoundary, h]

@[simp]
theorem componentProfileBoundary_single_of_not_mem {Θ : Type u} (Θ₀ : Set Θ)
    (θ : Θ) (h : θ ∉ Θ₀) :
    componentProfileBoundary Θ₀ (Finsupp.single θ 1) =
      Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Θ₀}) 1 := by
  classical
  simp [componentProfileBoundary, h]

/-- Label maps on `Θ` which vanish on the killed subobject. -/
abbrev VanishingComponentLabel (Θ₀ : Set Θ) (L : Type v) [AddCommMonoid L] :=
  {ell : Θ → L // ∀ θ, θ ∈ Θ₀ → ell θ = 0}

/-- The Hom universal property of the component-profile quotient. -/
noncomputable def componentProfileQuotient_hom_equiv {Θ : Type u} (Θ₀ : Set Θ)
    (L : Type v) [AddCommMonoid L] :
    (ComponentProfileQuotient Θ₀ →+ L) ≃ VanishingComponentLabel Θ₀ L := by
  classical
  exact {
  toFun f :=
    ⟨fun θ ↦ if h : θ ∈ Θ₀ then 0
      else f (Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Θ₀}) 1),
      fun θ h ↦ by simp [h]⟩
  invFun ell := componentLabelLift fun θ ↦ ell.1 θ.1
  left_inv f := by
    let labels : {θ : Θ // θ ∉ Θ₀} → L := fun θ ↦
      f (Finsupp.single θ 1)
    apply (componentLabelLift_existsUnique labels).unique
    · intro θ
      simp [labels, θ.property]
    · intro θ
      rfl
  right_inv ell := by
    apply Subtype.ext
    funext θ
    by_cases h : θ ∈ Θ₀
    · simp [h, ell.2 θ h]
    · simp [h]
  }

/-- The canonical equivalence with the free commutative monoid on the
complement of the killed component types. -/
noncomputable def componentProfileQuotient_equiv_freeComplement {Θ : Type u} (Θ₀ : Set Θ) :
    ComponentProfileQuotient Θ₀ ≃+ FCM {θ : Θ // θ ∉ Θ₀} :=
  AddEquiv.refl _

private theorem boundary_comp_killedComponentInclusion {Θ : Type u} (Θ₀ : Set Θ) :
    (componentProfileBoundary Θ₀).comp (killedComponentInclusion Θ₀) = 0 := by
  classical
  apply Finsupp.liftAddHom.symm.injective
  ext θ
  simp [killedComponentInclusion, componentProfileBoundary, θ.property]

private noncomputable def componentProfileQuotientDesc {Θ : Type u} (Θ₀ : Set Θ)
    {L : Type v} [AddCommMonoid L] (f : FCM Θ →+ L)
    (_hkill : f.comp (killedComponentInclusion Θ₀) = 0) :
    ComponentProfileQuotient Θ₀ →+ L :=
  componentLabelLift fun θ ↦ f (Finsupp.single θ.1 1)

private theorem componentProfileQuotientDesc_fac {Θ : Type u} (Θ₀ : Set Θ)
    {L : Type v} [AddCommMonoid L] (f : FCM Θ →+ L)
    (hkill : f.comp (killedComponentInclusion Θ₀) = 0) :
    (componentProfileQuotientDesc Θ₀ f hkill).comp (componentProfileBoundary Θ₀) = f := by
  classical
  apply Finsupp.liftAddHom.symm.injective
  ext θ
  by_cases hθ : θ ∈ Θ₀
  · have hz := DFunLike.congr_fun hkill (Finsupp.single (⟨θ, hθ⟩ : Θ₀) 1)
    simp [componentProfileBoundary, killedComponentInclusion, hθ] at hz ⊢
    exact hz.symm
  · simp [componentProfileQuotientDesc, componentProfileBoundary, hθ]

private theorem componentProfileQuotientDesc_unique {Θ : Type u} (Θ₀ : Set Θ)
    {L : Type v} [AddCommMonoid L] (f : FCM Θ →+ L)
    (hkill : f.comp (killedComponentInclusion Θ₀) = 0)
    (g : ComponentProfileQuotient Θ₀ →+ L)
    (hg : g.comp (componentProfileBoundary Θ₀) = f) :
    g = componentProfileQuotientDesc Θ₀ f hkill := by
  classical
  apply Finsupp.liftAddHom.symm.injective
  ext θ
  have h := DFunLike.congr_fun hg (Finsupp.single θ.1 1)
  simpa [Finsupp.liftAddHom_symm_apply_apply, componentProfileQuotientDesc,
    componentProfileBoundary, θ.property] using h

/-- The canonical cofork killing the selected component generators. -/
noncomputable def componentProfileQuotientCofork {Θ : Type u} (Θ₀ : Set Θ) :
    Cofork
      (AddCommMonCat.ofHom (killedComponentInclusion Θ₀))
      (AddCommMonCat.ofHom (0 : FCM Θ₀ →+ FCM Θ)) :=
  Cofork.ofπ (AddCommMonCat.ofHom (componentProfileBoundary Θ₀)) <| by
    apply AddCommMonCat.hom_ext
    simpa using boundary_comp_killedComponentInclusion Θ₀

private theorem cofork_kills_componentTypes {Θ : Type u} (Θ₀ : Set Θ)
    (s : Cofork
      (AddCommMonCat.ofHom (killedComponentInclusion Θ₀))
      (AddCommMonCat.ofHom (0 : FCM Θ₀ →+ FCM Θ))) :
    s.π.hom.comp (killedComponentInclusion Θ₀) = 0 := by
  simpa using congrArg AddCommMonCat.Hom.hom s.condition

/-- The displayed component-profile quotient is the required coequalizer. -/
noncomputable def componentProfileQuotient_isCoequalizer {Θ : Type u} (Θ₀ : Set Θ) :
    IsColimit (componentProfileQuotientCofork Θ₀) :=
  Cofork.IsColimit.mk _
    (fun s ↦ AddCommMonCat.ofHom <|
      componentProfileQuotientDesc Θ₀ s.π.hom (cofork_kills_componentTypes Θ₀ s))
    (fun s ↦ by
      apply AddCommMonCat.hom_ext
      change (componentProfileQuotientDesc Θ₀ s.π.hom
        (cofork_kills_componentTypes Θ₀ s)).comp (componentProfileBoundary Θ₀) = s.π.hom
      exact componentProfileQuotientDesc_fac Θ₀ s.π.hom _)
    (fun s m hm ↦ by
      apply AddCommMonCat.hom_ext
      apply componentProfileQuotientDesc_unique Θ₀ s.π.hom
        (cofork_kills_componentTypes Θ₀ s)
      change m.hom.comp (componentProfileBoundary Θ₀) = s.π.hom
      have h := congrArg AddCommMonCat.Hom.hom hm
      rw [AddCommMonCat.hom_comp] at h
      simpa [componentProfileQuotientCofork] using h)

end Erdos289
