import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.RelIso.Basic

/-!
# Reflexive symmetric graphs and connected components

The connected-component object is the quotient by Mathlib's equivalence closure
`Relation.EqvGen`; its universal property is packaged as the adjunction
`π₀ ⊣ Disc`.
-/

open CategoryTheory

namespace Erdos289

universe u

/-- A reflexive symmetric graph. -/
structure Graphᵣ where
  /-- The vertex type. -/
  carrier : Type u
  /-- The edge relation. -/
  Rel : carrier → carrier → Prop
  /-- Every vertex has a reflexive edge. -/
  refl : ∀ x, Rel x x
  /-- Edges are symmetric. -/
  symm : ∀ {x y}, Rel x y → Rel y x

namespace Graphᵣ

instance : CoeSort Graphᵣ (Type u) := ⟨Graphᵣ.carrier⟩

/-- A graph morphism is a wrapped Mathlib relation homomorphism. -/
structure Hom (G H : Graphᵣ) where
  /-- The underlying relation homomorphism. -/
  toRelHom : G.Rel →r H.Rel

instance : Category Graphᵣ where
  Hom := Hom
  id G := ⟨RelHom.id G.Rel⟩
  comp f g := ⟨g.toRelHom.comp f.toRelHom⟩
  assoc _ _ _ := rfl
  id_comp _ := rfl
  comp_id _ := rfl

instance {G H : Graphᵣ} : FunLike (G ⟶ H) G H where
  coe f := f.toRelHom
  coe_injective f g h := by
    cases f
    cases g
    congr
    exact RelHom.ext fun x ↦ congrFun h x

theorem Hom.map_rel {G H : Graphᵣ} (f : G ⟶ H) {x y : G} (h : G.Rel x y) :
    H.Rel (f x) (f y) :=
  f.toRelHom.map_rel h

@[ext]
theorem hom_ext {G H : Graphᵣ} {f g : G ⟶ H} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

end Graphᵣ

/-- The discrete reflexive graph functor. -/
def Disc : Type u ⥤ Graphᵣ.{u} where
  obj X :=
    { carrier := X
      Rel := Eq
      refl := fun _ ↦ rfl
      symm := Eq.symm }
  map f :=
    ⟨{ toFun := f
       map_rel' := fun h ↦ congrArg f h }⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The connected-component set of a reflexive graph. -/
abbrev PiZeroObj (G : Graphᵣ.{u}) := Quotient (Relation.EqvGen.setoid G.Rel)

/-- The canonical vertex-to-component quotient map. -/
def piZeroMk (G : Graphᵣ.{u}) : G → PiZeroObj G :=
  Quotient.mk (Relation.EqvGen.setoid G.Rel)

private theorem eqvGen_map {G H : Graphᵣ.{u}} (f : G ⟶ H) {x y : G} :
    Relation.EqvGen G.Rel x y → Relation.EqvGen H.Rel (f x) (f y) := by
  intro h
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (f.map_rel hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ hxy hyz => exact Relation.EqvGen.trans _ _ _ hxy hyz

/-- The map on connected components induced by a graph morphism. -/
def piZeroMap {G H : Graphᵣ.{u}} (f : G ⟶ H) : PiZeroObj G → PiZeroObj H :=
  Quotient.map f (fun _ _ h ↦ eqvGen_map f h)

@[simp]
theorem piZeroMap_mk {G H : Graphᵣ.{u}} (f : G ⟶ H) (x : G) :
    piZeroMap f (piZeroMk G x) = piZeroMk H (f x) :=
  rfl

/-- The connected-component functor. -/
def π₀ : Graphᵣ.{u} ⥤ Type u where
  obj G := PiZeroObj G
  map f := TypeCat.ofHom (piZeroMap f)
  map_id G := by
    apply ConcreteCategory.hom_ext
    intro z
    induction z using Quotient.inductionOn
    change piZeroMap (𝟙 G) (piZeroMk G _) = piZeroMk G _
    rw [piZeroMap_mk]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    induction z using Quotient.inductionOn
    change piZeroMap (f ≫ g) (piZeroMk _ _) =
      piZeroMap g (piZeroMap f (piZeroMk _ _))
    rw [piZeroMap_mk, piZeroMap_mk, piZeroMap_mk]
    rfl

private theorem edge_constant_eqvGen {G : Graphᵣ.{u}} {X : Type u}
    (f : G ⟶ Disc.obj X) {x y : G} :
    Relation.EqvGen G.Rel x y → f x = f y := by
  intro h
  induction h with
  | rel x y hxy => exact f.map_rel hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ hxy hyz => exact hxy.trans hyz

/-- A graph map to a discrete graph descends to connected components. -/
def piZero_desc {G : Graphᵣ.{u}} {X : Type u}
    (f : G ⟶ Disc.obj X) : π₀.obj G ⟶ X :=
  TypeCat.ofHom (Quotient.lift f fun _ _ h ↦ edge_constant_eqvGen f h)

@[simp]
theorem piZero_desc_mk {G : Graphᵣ.{u}} {X : Type u}
    (f : G ⟶ Disc.obj X) (x : G) :
    piZero_desc f (piZeroMk G x) = f x :=
  rfl

/-- Maps out of connected components are determined on vertex representatives. -/
theorem piZero_hom_ext {G : Graphᵣ.{u}} {X : Type u}
    {f g : π₀.obj G ⟶ X} (h : ∀ x : G, f (piZeroMk G x) = g (piZeroMk G x)) :
    f = g := by
  apply ConcreteCategory.hom_ext
  intro z
  induction z using Quotient.inductionOn
  exact h _

private def piZeroHomEquiv (G : Graphᵣ.{u}) (X : Type u) :
    (π₀.obj G ⟶ X) ≃ (G ⟶ Disc.obj X) where
  toFun f :=
    ⟨{ toFun := fun x ↦ f (piZeroMk G x)
       map_rel' := fun h ↦ congrArg f (Quotient.sound' (Relation.EqvGen.rel _ _ h)) }⟩
  invFun := piZero_desc
  left_inv f := by
    apply piZero_hom_ext
    intro x
    rfl
  right_inv f := by
    apply Graphᵣ.hom_ext
    intro x
    rfl

/-- Connected components are left adjoint to the discrete-graph embedding. -/
def piZeroAdjunction : π₀ ⊣ Disc :=
  Adjunction.mkOfHomEquiv
    { homEquiv := piZeroHomEquiv
      homEquiv_naturality_left_symm := fun f g ↦ by
        apply piZero_hom_ext
        intro x
        rfl
      homEquiv_naturality_right := fun f g ↦ by
        apply Graphᵣ.hom_ext
        intro x
        rfl }

end Erdos289

