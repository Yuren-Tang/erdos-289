module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import AffineCorrection.Physical
public import Erdos289.PathSupport
public import Mathlib.Combinatorics.SimpleGraph.Sum

@[expose] public section

/-!
# The partial union algebra of finite path supports

The multiplication domain consists of pairs whose induced graphs form a
disjoint union: the vertex sets are disjoint and there is no path edge joining
the two sides.  This is the graph-intrinsic condition that union does not merge
blocks; it is stronger information than a chosen decomposition of the union.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)

/-- A path in a graph coproduct whose endpoints lie on the left stays on the left. -/
theorem reachable_sum_inl_iff (v v' : V) :
    (G ⊕g H).Reachable (.inl v) (.inl v') ↔ G.Reachable v v' := by
  rw [reachable_iff_reflTransGen, reachable_iff_reflTransGen]
  constructor
  · intro h
    let aux : ∀ {x : V ⊕ W},
        Relation.ReflTransGen (G ⊕g H).Adj (.inl v) x →
          ∀ v' : V, x = .inl v' → Relation.ReflTransGen G.Adj v v' := by
      intro x hx
      induction hx with
      | refl =>
          intro v' hv'
          exact Sum.inl_injective hv' |>.symm ▸ .refl
      | @tail b c hbc hca ih =>
          intro v' hv'
          subst c
          cases b with
          | inl b =>
              simp only [sum_adj_inl] at hca
              exact (ih b rfl).tail hca
          | inr b =>
              simp at hca
    exact aux h v' rfl
  · intro h
    exact h.lift Sum.inl (by
      intro a b hab
      simpa using hab)

/-- A path in a graph coproduct whose endpoints lie on the right stays on the right. -/
theorem reachable_sum_inr_iff (w w' : W) :
    (G ⊕g H).Reachable (.inr w) (.inr w') ↔ H.Reachable w w' := by
  exact (Iso.reachable_iff (G := G ⊕g H) (G' := H ⊕g G)
    (φ := Iso.sumComm) (u := .inr w) (v := .inr w')).symm.trans
      (reachable_sum_inl_iff H G w w')

theorem map_sumInl_injective : Function.Injective
    (fun c : G.ConnectedComponent =>
      c.map (Embedding.sumInl (G := G) (H := H)).toHom) := by
  intro c d
  induction c using ConnectedComponent.ind with
  | _ v =>
      induction d using ConnectedComponent.ind with
      | _ v' =>
          intro h
          apply ConnectedComponent.sound
          apply (reachable_sum_inl_iff G H v v').mp
          apply ConnectedComponent.exact
          exact h

theorem map_sumInr_injective : Function.Injective
    (fun c : H.ConnectedComponent =>
      c.map (Embedding.sumInr (G := G) (H := H)).toHom) := by
  intro c d
  induction c using ConnectedComponent.ind with
  | _ w =>
      induction d using ConnectedComponent.ind with
      | _ w' =>
          intro h
          apply ConnectedComponent.sound
          apply (reachable_sum_inr_iff G H w w').mp
          apply ConnectedComponent.exact
          exact h

theorem map_sumInl_ne_map_sumInr
    (c : G.ConnectedComponent) (d : H.ConnectedComponent) :
    c.map (Embedding.sumInl (G := G) (H := H)).toHom ≠
      d.map (Embedding.sumInr (G := G) (H := H)).toHom := by
  induction c using ConnectedComponent.ind with
  | _ v =>
      induction d using ConnectedComponent.ind with
      | _ w =>
          intro h
          apply not_reachable_sum_inl_inr v w
          apply ConnectedComponent.exact
          exact h

/-- Connected components commute with graph coproducts. -/
noncomputable def connectedComponentSumEquiv :
    G.ConnectedComponent ⊕ H.ConnectedComponent ≃ (G ⊕g H).ConnectedComponent := by
  refine Equiv.ofBijective
    (Sum.elim
      (fun c => c.map (Embedding.sumInl (G := G) (H := H)).toHom)
      (fun c => c.map (Embedding.sumInr (G := G) (H := H)).toHom)) ?_
  constructor
  · intro c d hcd
    cases c with
    | inl c =>
        cases d with
        | inl d => exact congrArg Sum.inl (map_sumInl_injective G H hcd)
        | inr d => exact (map_sumInl_ne_map_sumInr G H c d hcd).elim
    | inr c =>
        cases d with
        | inl d => exact (map_sumInl_ne_map_sumInr G H d c hcd.symm).elim
        | inr d => exact congrArg Sum.inr (map_sumInr_injective G H hcd)
  · intro c
    induction c using ConnectedComponent.ind with
    | _ x =>
        cases x with
        | inl v => exact ⟨.inl (G.connectedComponentMk v), rfl⟩
        | inr w => exact ⟨.inr (H.connectedComponentMk w), rfl⟩

@[simp]
theorem connectedComponentSumEquiv_inl (c : G.ConnectedComponent) :
    connectedComponentSumEquiv G H (.inl c) =
      c.map (Embedding.sumInl (G := G) (H := H)).toHom :=
  rfl

@[simp]
theorem connectedComponentSumEquiv_inr (c : H.ConnectedComponent) :
    connectedComponentSumEquiv G H (.inr c) =
      c.map (Embedding.sumInr (G := G) (H := H)).toHom :=
  rfl

/-- A left component keeps its vertex cardinality in a graph coproduct. -/
theorem natCard_supp_connectedComponentSumEquiv_inl
    (c : G.ConnectedComponent) :
    Nat.card ((connectedComponentSumEquiv G H (.inl c)).supp) = Nat.card c.supp := by
  induction c using ConnectedComponent.ind with
  | _ v =>
      apply Nat.card_congr
      let e :
          ((connectedComponentSumEquiv G H
            (.inl (G.connectedComponentMk v))).supp) ≃
            (G.connectedComponentMk v).supp := {
        toFun x := by
          rcases hxv : x.1 with u | w
          · refine ⟨u, ?_⟩
            rw [ConnectedComponent.mem_supp_iff]
            have hx := x.property
            rw [ConnectedComponent.mem_supp_iff] at hx
            have he : connectedComponentSumEquiv G H
                (.inl (G.connectedComponentMk v)) =
                (G ⊕g H).connectedComponentMk (.inl v) := by simp
            have hx' := hx.trans he
            rw [hxv] at hx'
            exact ConnectedComponent.sound <|
              (reachable_sum_inl_iff G H u v).mp (ConnectedComponent.exact hx')
          · have hx := x.property
            rw [ConnectedComponent.mem_supp_iff] at hx
            have he : connectedComponentSumEquiv G H
                (.inl (G.connectedComponentMk v)) =
                (G ⊕g H).connectedComponentMk (.inl v) := by simp
            have hx' := hx.trans he
            rw [hxv] at hx'
            exact (not_reachable_sum_inl_inr v w
              (ConnectedComponent.exact hx').symm).elim
        invFun x := ⟨.inl x.1, by
          have hx := x.property
          rw [ConnectedComponent.mem_supp_iff] at hx ⊢
          have he : connectedComponentSumEquiv G H
              (.inl (G.connectedComponentMk v)) =
              (G ⊕g H).connectedComponentMk (.inl v) := by simp
          exact (ConnectedComponent.sound
            ((reachable_sum_inl_iff G H x.1 v).mpr
              (ConnectedComponent.exact hx))).trans he.symm⟩
        left_inv x := by
          rcases x with ⟨u | w, hu⟩
          · rfl
          · rw [ConnectedComponent.mem_supp_iff] at hu
            change (G ⊕g H).connectedComponentMk (.inr w) =
              (G ⊕g H).connectedComponentMk (.inl v) at hu
            exact (not_reachable_sum_inl_inr v w
              (ConnectedComponent.exact hu).symm).elim
        right_inv x := rfl }
      exact e

/-- A right component keeps its vertex cardinality in a graph coproduct. -/
theorem natCard_supp_connectedComponentSumEquiv_inr
    (c : H.ConnectedComponent) :
    Nat.card ((connectedComponentSumEquiv G H (.inr c)).supp) = Nat.card c.supp := by
  induction c using ConnectedComponent.ind with
  | _ w =>
      apply Nat.card_congr
      let e :
          ((connectedComponentSumEquiv G H
            (.inr (H.connectedComponentMk w))).supp) ≃
            (H.connectedComponentMk w).supp := {
        toFun x := by
          rcases hxv : x.1 with v | u
          · have hx := x.property
            rw [ConnectedComponent.mem_supp_iff] at hx
            have he : connectedComponentSumEquiv G H
                (.inr (H.connectedComponentMk w)) =
                (G ⊕g H).connectedComponentMk (.inr w) := by simp
            have hx' := hx.trans he
            rw [hxv] at hx'
            exact (not_reachable_sum_inl_inr v w
              (ConnectedComponent.exact hx')).elim
          · refine ⟨u, ?_⟩
            rw [ConnectedComponent.mem_supp_iff]
            have hx := x.property
            rw [ConnectedComponent.mem_supp_iff] at hx
            have he : connectedComponentSumEquiv G H
                (.inr (H.connectedComponentMk w)) =
                (G ⊕g H).connectedComponentMk (.inr w) := by simp
            have hx' := hx.trans he
            rw [hxv] at hx'
            exact ConnectedComponent.sound <|
              (reachable_sum_inr_iff G H u w).mp (ConnectedComponent.exact hx')
        invFun x := ⟨.inr x.1, by
          have hx := x.property
          rw [ConnectedComponent.mem_supp_iff] at hx ⊢
          have he : connectedComponentSumEquiv G H
              (.inr (H.connectedComponentMk w)) =
              (G ⊕g H).connectedComponentMk (.inr w) := by simp
          exact (ConnectedComponent.sound
            ((reachable_sum_inr_iff G H x.1 w).mpr
              (ConnectedComponent.exact hx))).trans he.symm⟩
        left_inv x := by
          rcases x with ⟨v | u, hu⟩
          · rw [ConnectedComponent.mem_supp_iff] at hu
            change (G ⊕g H).connectedComponentMk (.inl v) =
              (G ⊕g H).connectedComponentMk (.inr w) at hu
            exact (not_reachable_sum_inl_inr v w
              (ConnectedComponent.exact hu)).elim
          · rfl
        right_inv x := rfl }
      exact e

/-- The number of components of a graph coproduct is the sum of the two counts. -/
theorem natCard_connectedComponent_sum [Finite V] [Finite W] :
    Nat.card (G ⊕g H).ConnectedComponent =
      Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
  rw [← Nat.card_sum]
  exact Nat.card_congr (connectedComponentSumEquiv G H).symm

end SimpleGraph

namespace Erdos289

/-- Two supports form a graph-theoretic disjoint union. -/
def Support.GraphDisjoint (S T : Support) : Prop :=
  Disjoint S T ∧
    ∀ a ∈ S, ∀ b ∈ T, ¬denominatorPath.Adj a b

namespace Support.GraphDisjoint

theorem symm {S T : Support} (h : S.GraphDisjoint T) : T.GraphDisjoint S := by
  refine ⟨h.1.symm, ?_⟩
  intro b hb a ha hab
  exact h.2 a ha b hb (denominatorPath.symm.symm b a hab)

@[simp]
theorem empty_left (S : Support) : (∅ : Support).GraphDisjoint S := by
  simp [Support.GraphDisjoint]

@[simp]
theorem empty_right (S : Support) : S.GraphDisjoint (∅ : Support) :=
  (empty_left S).symm

theorem union_left_iff {R S T : Support} :
    (R ∪ S).GraphDisjoint T ↔ R.GraphDisjoint T ∧ S.GraphDisjoint T := by
  constructor
  · rintro ⟨hdisj, hedge⟩
    have hR : Disjoint R T := Finset.disjoint_of_subset_left Finset.subset_union_left hdisj
    have hS : Disjoint S T := Finset.disjoint_of_subset_left Finset.subset_union_right hdisj
    refine ⟨⟨hR, ?_⟩, ⟨hS, ?_⟩⟩
    · intro a ha b hb
      exact hedge a (Finset.mem_union_left S ha) b hb
    · intro a ha b hb
      exact hedge a (Finset.mem_union_right R ha) b hb
  · rintro ⟨⟨hRT, hRedge⟩, ⟨hST, hSedge⟩⟩
    refine ⟨?_, ?_⟩
    · simpa [Finset.disjoint_union_left] using And.intro hRT hST
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hRedge a ha b hb
      · exact hSedge a ha b hb

theorem union_right_iff {R S T : Support} :
    R.GraphDisjoint (S ∪ T) ↔ R.GraphDisjoint S ∧ R.GraphDisjoint T := by
  rw [show R.GraphDisjoint (S ∪ T) ↔ (S ∪ T).GraphDisjoint R from
    ⟨fun h => h.symm, fun h => h.symm⟩]
  rw [union_left_iff]
  exact and_congr (Iff.intro symm symm) (Iff.intro symm symm)

end Support.GraphDisjoint

/-- A graph-disjoint union is the coproduct of the two induced support graphs. -/
noncomputable def Support.GraphDisjoint.unionGraphIso
    {S T : Support} (h : S.GraphDisjoint T) :
    S.graph ⊕g T.graph ≃g (S ∪ T).graph where
  toEquiv := Equiv.Finset.union S T h.1
  map_rel_iff' := by
    rintro (x | x) (y | y)
    · rfl
    · simp only [Equiv.Finset.union_inl, Equiv.Finset.union_inr,
        Support.graph, SimpleGraph.induce_adj, SimpleGraph.sum_adj]
      exact iff_false_intro (h.2 x x.property y y.property)
    · simp only [Equiv.Finset.union_inl, Equiv.Finset.union_inr]
      simp only [Support.graph, SimpleGraph.induce_adj, SimpleGraph.sum_adj]
      exact iff_false_intro (fun hxy =>
        h.2 y y.property x x.property (denominatorPath.symm.symm x y hxy))
    · rfl

/-- Component grade is additive on graph-disjoint support unions. -/
theorem Support.grade_union_of_graphDisjoint
    {S T : Support} (h : S.GraphDisjoint T) :
    (S ∪ T).grade = S.grade + T.grade := by
  rw [Support.grade, Support.grade, Support.grade]
  rw [← SimpleGraph.natCard_connectedComponent_sum]
  exact Nat.card_congr h.unionGraphIso.connectedComponentEquiv.symm

/-- Allowed component sizes are preserved by graph-disjoint union. -/
theorem Support.hasBlockSizes_union
    {S T : Support} {L : Set ℕ}
    (h : S.GraphDisjoint T)
    (hS : S.HasBlockSizes L) (hT : T.HasBlockSizes L) :
    (S ∪ T).HasBlockSizes L := by
  intro c
  let φ : S.graph ⊕g T.graph ≃g (S ∪ T).graph := h.unionGraphIso
  let cs := φ.symm.connectedComponentEquiv c
  let side := (SimpleGraph.connectedComponentSumEquiv S.graph T.graph).symm cs
  have hcs : SimpleGraph.connectedComponentSumEquiv S.graph T.graph side = cs :=
    (SimpleGraph.connectedComponentSumEquiv S.graph T.graph).apply_symm_apply cs
  cases hside : side with
  | inl d =>
      have hcard₁ : Nat.card c.supp = Nat.card cs.supp :=
        Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp φ.symm c)
      have hcard₂ : Nat.card cs.supp = Nat.card d.supp := by
        rw [← hcs, hside]
        exact SimpleGraph.natCard_supp_connectedComponentSumEquiv_inl S.graph T.graph d
      change Nat.card c.supp ∈ L
      rw [hcard₁, hcard₂]
      exact hS d
  | inr d =>
      have hcard₁ : Nat.card c.supp = Nat.card cs.supp :=
        Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp φ.symm c)
      have hcard₂ : Nat.card cs.supp = Nat.card d.supp := by
        rw [← hcs, hside]
        exact SimpleGraph.natCard_supp_connectedComponentSumEquiv_inr S.graph T.graph d
      change Nat.card c.supp ∈ L
      rw [hcard₁, hcard₂]
      exact hT d

/-- Every point of the left support embeds into the union support graph. -/
def Support.graphHomUnionLeft (S T : Support) : S.graph →g (S ∪ T).graph where
  toFun x := ⟨x.1, Finset.mem_union_left T x.2⟩
  map_rel' h := h

/-- Every point of the right support embeds into the union support graph. -/
def Support.graphHomUnionRight (S T : Support) : T.graph →g (S ∪ T).graph where
  toFun x := ⟨x.1, Finset.mem_union_right S x.2⟩
  map_rel' h := h

/--
Equivalent pointwise form of component separation: points at distance at most
the margin must lie in the same connected component.
-/
theorem Support.separated_iff_close_reachable (S : Support) (margin : ℕ) :
    S.Separated margin ↔
      ∀ x y : {n : Denominator // n ∈ S},
        Nat.dist x.1.1 y.1.1 ≤ margin → S.graph.Reachable x y := by
  constructor
  · intro hsep x y hclose
    by_contra hreach
    have hcomp : S.graph.connectedComponentMk x ≠
        S.graph.connectedComponentMk y := by
      intro heq
      exact hreach (SimpleGraph.ConnectedComponent.exact heq)
    have hfar := hsep (S.graph.connectedComponentMk x)
      (S.graph.connectedComponentMk y) hcomp x (by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]) y (by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff])
    omega
  · intro hclose c d hcd x hx y hy
    by_contra hfar
    have hreach := hclose x y (by omega)
    apply hcd
    have hxc : S.graph.connectedComponentMk x = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
    have hyd : S.graph.connectedComponentMk y = d :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff d y).mp hy
    exact hxc.symm.trans <|
      (SimpleGraph.ConnectedComponent.sound hreach).trans hyd

/-- Cross-support point separation used when composing admissible supports. -/
def Support.CrossSeparated (S T : Support) (margin : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, margin < Nat.dist x.1 y.1

/--
Translated-window separation.  Two supports confined to windows of the same
length `d` are cross-separated by `m` as soon as the windows' left endpoints
are more than `m + d` apart.  The separation constants of concrete block
patterns are instances of this with `d` their diameter.
-/
theorem Support.crossSeparated_of_window
    {S T : Support} {a b d m : ℕ}
    (hS : ∀ x ∈ S, a ≤ x.1 ∧ x.1 ≤ a + d)
    (hT : ∀ y ∈ T, b ≤ y.1 ∧ y.1 ≤ b + d)
    (h : m + d < Nat.dist a b) :
    S.CrossSeparated T m := by
  intro x hx y hy
  obtain ⟨hxa, hxb⟩ := hS x hx
  obtain ⟨hya, hyb⟩ := hT y hy
  rcases le_total a b with hab | hab
  · rw [Nat.dist_eq_sub_of_le hab] at h
    rw [Nat.dist_eq_sub_of_le (show x.1 ≤ y.1 by omega)]
    omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hab] at h
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (show y.1 ≤ x.1 by omega)]
    omega

/-- Component separation is preserved by a sufficiently separated union. -/
theorem Support.separated_union
    {S T : Support} {margin : ℕ}
    (hS : S.Separated margin) (hT : T.Separated margin)
    (hcross : S.CrossSeparated T margin) :
    (S ∪ T).Separated margin := by
  rw [Support.separated_iff_close_reachable]
  intro x y hxy
  rcases Finset.mem_union.mp x.2 with hxS | hxT <;>
    rcases Finset.mem_union.mp y.2 with hyS | hyT
  · have hr := (Support.separated_iff_close_reachable S margin).mp hS
        ⟨x.1, hxS⟩ ⟨y.1, hyS⟩ hxy
    exact hr.map (Support.graphHomUnionLeft S T)
  · exact (not_lt_of_ge hxy (hcross x.1 hxS y.1 hyT)).elim
  · have hfar := hcross y.1 hyS x.1 hxT
    rw [Nat.dist_comm] at hfar
    exact (not_lt_of_ge hxy hfar).elim
  · have hr := (Support.separated_iff_close_reachable T margin).mp hT
        ⟨x.1, hxT⟩ ⟨y.1, hyT⟩ hxy
    exact hr.map (Support.graphHomUnionRight S T)

/-- Obstacle avoidance is preserved by union. -/
theorem Support.avoids_union
    {S T : Support} {c : PhysicalConstraint}
    (hS : S.Avoids c) (hT : T.Avoids c) :
    (S ∪ T).Avoids c := by
  simpa [Support.Avoids, Finset.disjoint_union_left] using And.intro hS hT

theorem crossSeparated_mono {S T : Support} {m n : ℕ}
    (h : S.CrossSeparated T n) (hmn : m ≤ n) : S.CrossSeparated T m := by
  intro x hx y hy
  exact lt_of_le_of_lt hmn (h x hx y hy)

/-- Distance greater than one excludes both shared vertices and path edges. -/
theorem crossSeparated_graphDisjoint {S T : Support}
    (h : S.CrossSeparated T 1) : S.GraphDisjoint T := by
  constructor
  · rw [Finset.disjoint_left]
    intro x hxS hxT
    have := h x hxS x hxT
    simp at this
  · intro x hx y hy hadj
    have hdist : Nat.dist x.1 y.1 = 1 := by
      change x.1 + 1 = y.1 ∨ y.1 + 1 = x.1 at hadj
      rcases hadj with hadj | hadj
      · rw [Nat.dist_eq_sub_of_le (by omega)]
        omega
      · rw [Nat.dist_eq_sub_of_le_right (by omega)]
        omega
    have := h x hx y hy
    omega

/-- The admissible-support subobject is closed under separated graph-disjoint union. -/
theorem Support.admissible_union
    {S T : Support} {L : Set ℕ} {c : PhysicalConstraint}
    (hdisj : S.GraphDisjoint T)
    (hcross : S.CrossSeparated T c.separation)
    (hS : S.Admissible L c) (hT : T.Admissible L c) :
    (S ∪ T).Admissible L c :=
  ⟨Support.hasBlockSizes_union hdisj hS.1 hT.1,
    Support.avoids_union hS.2.1 hT.2.1,
    Support.separated_union hS.2.2 hT.2.2 hcross⟩

/-- Graph of the partial union operation on finite path supports. -/
def Support.Compose (S T U : Support) : Prop :=
  S.GraphDisjoint T ∧ U = S ∪ T

/-- Finite path supports with graph-disjoint union as partial addition. -/
def supportPCM : AffineCorrection.PartialAddCommMonoid Support where
  zero := ∅
  add := Support.Compose
  functional := by
    rintro S T U U' ⟨_, rfl⟩ ⟨_, hU'⟩
    exact hU'.symm
  zero_add := by
    intro S
    exact ⟨Support.GraphDisjoint.empty_left S, by simp⟩
  add_comm := by
    rintro S T U ⟨h, hU⟩
    exact ⟨h.symm, hU.trans (Finset.union_comm S T)⟩
  add_assoc := by
    intro R S T U
    constructor
    · rintro ⟨RS, ⟨hRS, rfl⟩, ⟨hRST, rfl⟩⟩
      rw [Support.GraphDisjoint.union_left_iff] at hRST
      refine ⟨S ∪ T, ⟨hRST.2, rfl⟩, ?_⟩
      refine ⟨?_, Finset.union_assoc R S T⟩
      rw [Support.GraphDisjoint.union_right_iff]
      exact ⟨hRS, hRST.1⟩
    · rintro ⟨ST, ⟨hST, rfl⟩, ⟨hRST, rfl⟩⟩
      rw [Support.GraphDisjoint.union_right_iff] at hRST
      refine ⟨R ∪ S, ⟨hRST.1, rfl⟩, ?_⟩
      refine ⟨?_, (Finset.union_assoc R S T).symm⟩
      rw [Support.GraphDisjoint.union_left_iff]
      exact ⟨hRST.2, hST⟩

/-- Reciprocal value is additive on every defined physical union. -/
theorem support_value_additive :
    AffineCorrection.IsAdditiveOn supportPCM Support.value := by
  rintro S T U ⟨h, rfl⟩
  exact Support.value_union h.1

/-- Connected-component grade is additive on every defined physical union. -/
theorem support_grade_additive :
    AffineCorrection.IsAdditiveOn supportPCM Support.grade := by
  rintro S T U ⟨h, rfl⟩
  exact Support.grade_union_of_graphDisjoint h

end Erdos289
