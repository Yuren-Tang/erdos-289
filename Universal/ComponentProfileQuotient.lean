import Universal.FiniteComponentState

import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.Data.Finsupp.Basic

/-!
# Quotients of component profiles

The public construction kills an arbitrary embedded subobject of component
types.  For a literal subset, it is canonically identified with the free
commutative monoid on the set-theoretic complement.
-/

open CategoryTheory CategoryTheory.Limits

namespace Erdos289

universe u v w

/-- The component-profile quotient killing the image of an arbitrary
component-type subobject. -/
abbrev ComponentProfileQuotient {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ) :=
  FCM {θ : Θ // θ ∉ Set.range j}

/-- Inclusion of the killed generators into the full free commutative monoid. -/
noncomputable def killedComponentInclusion {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ) :
    FCM Θ₀ →+ FCM Θ :=
  componentLabelLift fun θ₀ ↦ Finsupp.single (j θ₀) 1

/-- The canonical boundary map which deletes precisely the image of the killed
subobject. -/
noncomputable def componentProfileBoundary {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ) :
    FCM Θ →+ ComponentProfileQuotient j := by
  classical
  exact componentLabelLift fun θ ↦
    if h : θ ∈ Set.range j then 0
    else Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Set.range j}) 1

@[simp]
theorem componentProfileBoundary_single_of_mem_range {Θ₀ : Type v} {Θ : Type u}
    (j : Θ₀ ↪ Θ) (θ : Θ) (h : θ ∈ Set.range j) :
    componentProfileBoundary j (Finsupp.single θ 1) = 0 := by
  classical
  rw [componentProfileBoundary, componentLabelLift_single]
  rw [dif_pos h]

@[simp]
theorem componentProfileBoundary_single_embedding {Θ₀ : Type v} {Θ : Type u}
    (j : Θ₀ ↪ Θ) (θ₀ : Θ₀) :
    componentProfileBoundary j (Finsupp.single (j θ₀) 1) = 0 :=
  componentProfileBoundary_single_of_mem_range j _ ⟨θ₀, rfl⟩

@[simp]
theorem componentProfileBoundary_single_of_not_mem_range {Θ₀ : Type v} {Θ : Type u}
    (j : Θ₀ ↪ Θ) (θ : Θ) (h : θ ∉ Set.range j) :
    componentProfileBoundary j (Finsupp.single θ 1) =
      Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Set.range j}) 1 := by
  classical
  rw [componentProfileBoundary, componentLabelLift_single]
  rw [dif_neg h]

/-- Label maps on the ambient component types which vanish on the embedded
subobject. -/
abbrev VanishingComponentLabel {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ)
    (L : Type w) [AddCommMonoid L] :=
  {ell : Θ → L // ∀ θ₀, ell (j θ₀) = 0}

/-- The Hom universal property of the component-profile quotient. -/
noncomputable def componentProfileQuotient_hom_equiv
    {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ)
    (L : Type w) [AddCommMonoid L] :
    (ComponentProfileQuotient j →+ L) ≃ VanishingComponentLabel j L := by
  classical
  exact {
    toFun f :=
      ⟨fun θ ↦ if h : θ ∈ Set.range j then 0
        else f (Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Set.range j}) 1),
        fun θ₀ ↦ by simp [Set.mem_range]⟩
    invFun ell := componentLabelLift fun θ ↦ ell.1 θ.1
    left_inv f := by
      let labels : {θ : Θ // θ ∉ Set.range j} → L := fun θ ↦
        f (Finsupp.single θ 1)
      apply (componentLabelLift_existsUnique labels).unique
      · intro θ
        rw [componentLabelLift_single]
        change (if h : θ.1 ∈ Set.range j then 0
          else f (Finsupp.single ⟨θ.1, h⟩ 1)) = labels θ
        rw [dif_neg θ.property]
      · intro θ
        rfl
    right_inv ell := by
      apply Subtype.ext
      funext θ
      by_cases h : θ ∈ Set.range j
      · obtain ⟨θ₀, rfl⟩ := h
        simp [ell.2 θ₀]
      · simp [h]
  }

/-- Postcomposition sends a vanishing component label to a vanishing label. -/
def VanishingComponentLabel.map
    {Θ₀ : Type v} {Θ : Type u} {L : Type w} {L' : Type*}
    [AddCommMonoid L] [AddCommMonoid L'] (j : Θ₀ ↪ Θ)
    (g : L →+ L') (ell : VanishingComponentLabel j L) :
    VanishingComponentLabel j L' :=
  ⟨fun θ ↦ g (ell.1 θ), fun θ₀ ↦ by
    change g (ell.1 (j θ₀)) = 0
    rw [ell.2 θ₀, map_zero]⟩

/-- The Hom universal-property equivalence is natural in the target
commutative monoid: its square with postcomposition commutes. -/
theorem componentProfileQuotient_hom_equiv_natural
    {Θ₀ : Type v} {Θ : Type u} {L : Type w} {L' : Type*}
    [AddCommMonoid L] [AddCommMonoid L'] (j : Θ₀ ↪ Θ)
    (g : L →+ L') (f : ComponentProfileQuotient j →+ L) :
    componentProfileQuotient_hom_equiv j L' (g.comp f) =
      VanishingComponentLabel.map j g
        (componentProfileQuotient_hom_equiv j L f) := by
  classical
  apply Subtype.ext
  funext θ
  change (if h : θ ∈ Set.range j then 0
      else g (f (Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Set.range j}) 1))) =
    g (if h : θ ∈ Set.range j then 0
      else f (Finsupp.single (⟨θ, h⟩ : {θ // θ ∉ Set.range j}) 1))
  by_cases hθ : θ ∈ Set.range j <;> simp [hθ]

/-- The embedding associated with a literal subset of component types. -/
def componentTypeSubsetEmbedding {Θ : Type u} (Θ₀ : Set Θ) : Θ₀ ↪ Θ :=
  ⟨Subtype.val, Subtype.val_injective⟩

private def complementRangeSubsetEquiv {Θ : Type u} (Θ₀ : Set Θ) :
    {θ : Θ // θ ∉ Set.range (componentTypeSubsetEmbedding Θ₀)} ≃
      {θ : Θ // θ ∉ Θ₀} where
  toFun θ := ⟨θ.1, fun hθ ↦ θ.2 ⟨⟨θ.1, hθ⟩, rfl⟩⟩
  invFun θ := ⟨θ.1, by
    rintro ⟨θ₀, hθ₀⟩
    exact θ.2 (hθ₀ ▸ θ₀.2)⟩
  left_inv θ := Subtype.ext rfl
  right_inv θ := Subtype.ext rfl

/-- For a literal subset, the arbitrary-subobject quotient is canonically the
free commutative monoid on its literal complement. -/
noncomputable def componentProfileQuotient_equiv_freeComplement
    {Θ : Type u} (Θ₀ : Set Θ) :
    ComponentProfileQuotient (componentTypeSubsetEmbedding Θ₀) ≃+
      FCM {θ : Θ // θ ∉ Θ₀} :=
  Finsupp.domCongr (complementRangeSubsetEquiv Θ₀)

/-- The canonical complement presentation specialized to a literal subset. -/
abbrev LiteralComponentProfileQuotient {Θ : Type u} (Θ₀ : Set Θ) :=
  ComponentProfileQuotient (componentTypeSubsetEmbedding Θ₀)

private theorem boundary_comp_killedComponentInclusion
    {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ) :
    (componentProfileBoundary j).comp (killedComponentInclusion j) = 0 := by
  classical
  apply Finsupp.liftAddHom.symm.injective
  ext θ₀
  simp [killedComponentInclusion, componentProfileBoundary]

private noncomputable def componentProfileQuotientDesc
    {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ)
    {L : Type w} [AddCommMonoid L] (f : FCM Θ →+ L)
    (_hkill : f.comp (killedComponentInclusion j) = 0) :
    ComponentProfileQuotient j →+ L :=
  componentLabelLift fun θ ↦ f (Finsupp.single θ.1 1)

private theorem componentProfileQuotientDesc_fac
    {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ)
    {L : Type w} [AddCommMonoid L] (f : FCM Θ →+ L)
    (hkill : f.comp (killedComponentInclusion j) = 0) :
    (componentProfileQuotientDesc j f hkill).comp (componentProfileBoundary j) = f := by
  classical
  apply (componentLabelLift_existsUnique
    (fun θ ↦ f (Finsupp.single θ 1))).unique
  · intro θ
    change componentProfileQuotientDesc j f hkill
      (componentProfileBoundary j (Finsupp.single θ 1)) =
        f (Finsupp.single θ 1)
    by_cases hθ : θ ∈ Set.range j
    · obtain ⟨θ₀, rfl⟩ := hθ
      have hz := DFunLike.congr_fun hkill (Finsupp.single θ₀ 1)
      simp [componentProfileBoundary, killedComponentInclusion] at hz ⊢
      exact hz.symm
    · rw [componentProfileBoundary, componentLabelLift_single, dif_neg hθ]
      simp [componentProfileQuotientDesc]
  · intro θ
    rfl

private theorem componentProfileQuotientDesc_unique
    {Θ₀ : Type v} {Θ : Type u} (j : Θ₀ ↪ Θ)
    {L : Type w} [AddCommMonoid L] (f : FCM Θ →+ L)
    (hkill : f.comp (killedComponentInclusion j) = 0)
    (g : ComponentProfileQuotient j →+ L)
    (hg : g.comp (componentProfileBoundary j) = f) :
    g = componentProfileQuotientDesc j f hkill := by
  classical
  apply Finsupp.liftAddHom.symm.injective
  ext θ
  have h := DFunLike.congr_fun hg (Finsupp.single θ.1 1)
  change g (componentProfileBoundary j (Finsupp.single θ.1 1)) =
    f (Finsupp.single θ.1 1) at h
  rw [componentProfileBoundary, componentLabelLift_single, dif_neg θ.property] at h
  simpa [Finsupp.liftAddHom_symm_apply_apply, componentProfileQuotientDesc,
    componentProfileBoundary] using h

/-- The canonical cofork killing the embedded component generators. -/
noncomputable def componentProfileQuotientCofork
    {Θ₀ : Type u} {Θ : Type u} (j : Θ₀ ↪ Θ) :
    Cofork
      (AddCommMonCat.ofHom (killedComponentInclusion j))
      (AddCommMonCat.ofHom (0 : FCM Θ₀ →+ FCM Θ)) :=
  Cofork.ofπ (AddCommMonCat.ofHom (componentProfileBoundary j)) <| by
    apply AddCommMonCat.hom_ext
    simpa using boundary_comp_killedComponentInclusion j

private theorem cofork_kills_componentTypes
    {Θ₀ : Type u} {Θ : Type u} (j : Θ₀ ↪ Θ)
    (s : Cofork
      (AddCommMonCat.ofHom (killedComponentInclusion j))
      (AddCommMonCat.ofHom (0 : FCM Θ₀ →+ FCM Θ))) :
    s.π.hom.comp (killedComponentInclusion j) = 0 := by
  simpa using congrArg AddCommMonCat.Hom.hom s.condition

/-- The displayed component-profile quotient is the required coequalizer. -/
noncomputable def componentProfileQuotient_isCoequalizer
    {Θ₀ : Type u} {Θ : Type u} (j : Θ₀ ↪ Θ) :
    IsColimit (componentProfileQuotientCofork j) :=
  Cofork.IsColimit.mk _
    (fun s ↦ AddCommMonCat.ofHom <|
      componentProfileQuotientDesc j s.π.hom (cofork_kills_componentTypes j s))
    (fun s ↦ by
      apply AddCommMonCat.hom_ext
      change (componentProfileQuotientDesc j s.π.hom
        (cofork_kills_componentTypes j s)).comp (componentProfileBoundary j) = s.π.hom
      exact componentProfileQuotientDesc_fac j s.π.hom _)
    (fun s m hm ↦ by
      apply AddCommMonCat.hom_ext
      apply componentProfileQuotientDesc_unique j s.π.hom
        (cofork_kills_componentTypes j s)
      change m.hom.comp (componentProfileBoundary j) = s.π.hom
      have h := congrArg AddCommMonCat.Hom.hom hm
      rw [AddCommMonCat.hom_comp] at h
      simpa [componentProfileQuotientCofork] using h)

end Erdos289
