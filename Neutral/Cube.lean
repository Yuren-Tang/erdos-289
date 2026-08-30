import Neutral.Fibres

/-!
# Leaf N — finite neutral cubes

The neutral-type object `{e₂, e₃-e₂}`, the neutral coordinate object attached to
a neutral type, a positive rational resource bound and a finite physical
constraint, and the finite neutral cube with its selectorwise direct n-ary
compatibility field.
-/

open scoped BigOperators

namespace Erdos289

set_option linter.style.haveILetI false

/-! ## Direct compatibility of separated families -/

/-- Constraint admissibility is antitone in the constraint. -/
theorem constraintAdmissible_mono {c c' : PhysicalConstraint} (h : c ≤ c')
    {S : E289State} (hS : ConstraintAdmissible c' S) : ConstraintAdmissible c S :=
  ⟨fun e he v hv ↦ lt_of_le_of_lt h.2 (hS.1 e (h.1 he) v hv),
    fun u v huv ↦ lt_of_le_of_lt h.2 (hS.2 u v huv)⟩

variable {I : Type} [Fintype I]

omit [Fintype I] in
/-- Along a chain in the ambient union of a separated family, membership in one
member state is preserved, together with connectedness inside that state. -/
private theorem eqvGen_within (S : I → E289State)
    (hsep : ∀ i j : I, i ≠ j → ∀ u ∈ (S i).support, ∀ w ∈ (S j).support,
      2 ≤ successorDist u w) (k : I) :
    ∀ x y : (narySupport S : Set successorGraph),
      Relation.EqvGen (inducedGraph successorGraph (narySupport S)).Rel x y →
      (∀ hx : x.1 ∈ (S k).support, ∃ hy : y.1 ∈ (S k).support,
          Relation.EqvGen (S k).graph.Rel ⟨x.1, hx⟩ ⟨y.1, hy⟩) ∧
      (∀ hy : y.1 ∈ (S k).support, ∃ hx : x.1 ∈ (S k).support,
          Relation.EqvGen (S k).graph.Rel ⟨x.1, hx⟩ ⟨y.1, hy⟩) := by
  intro x y h
  induction h with
  | rel a b hab =>
      have hstep : ∀ u v : (narySupport S : Set successorGraph),
          successorDist u.1 v.1 ≤ 1 → u.1 ∈ (S k).support → v.1 ∈ (S k).support := by
        intro u v huv hu
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 v.2
        by_cases hjk : j = k
        · exact hjk ▸ hj
        · exfalso
          have hc := successorDist_comm v.1 u.1
          have hd := hsep j k hjk _ hj _ hu
          omega
      have hab' : successorDist a.1 b.1 ≤ 1 := hab
      have hba : successorDist b.1 a.1 ≤ 1 := by
        have hc := successorDist_comm a.1 b.1
        omega
      refine ⟨fun hx ↦ ⟨hstep a b hab' hx, Relation.EqvGen.rel _ _ hab⟩,
        fun hy ↦ ⟨hstep b a hba hy, Relation.EqvGen.rel _ _ hab⟩⟩
  | refl a => exact ⟨fun hx ↦ ⟨hx, Relation.EqvGen.refl _⟩,
      fun hy ↦ ⟨hy, Relation.EqvGen.refl _⟩⟩
  | symm a b _ ih =>
      refine ⟨fun hx ↦ ?_, fun hy ↦ ?_⟩
      · obtain ⟨hy, hgen⟩ := ih.2 hx
        exact ⟨hy, Relation.EqvGen.symm _ _ hgen⟩
      · obtain ⟨hx, hgen⟩ := ih.1 hy
        exact ⟨hx, Relation.EqvGen.symm _ _ hgen⟩
  | trans a b c _ _ ih1 ih2 =>
      refine ⟨fun hx ↦ ?_, fun hz ↦ ?_⟩
      · obtain ⟨hb, h1⟩ := ih1.1 hx
        obtain ⟨hc, h2⟩ := ih2.1 hb
        exact ⟨hc, Relation.EqvGen.trans _ _ _ h1 h2⟩
      · obtain ⟨hb, h2⟩ := ih2.2 hz
        obtain ⟨ha, h1⟩ := ih1.2 hb
        exact ⟨ha, Relation.EqvGen.trans _ _ _ h1 h2⟩

omit [Fintype I] in
/-- A family of states whose supports are pairwise separated by graph distance at
least two factors through the direct n-ary physical compatibility locus. -/
theorem naryCompatible_of_separated (S : I → E289State)
    (hsep : ∀ i j : I, i ≠ j → ∀ u ∈ (S i).support, ∀ w ∈ (S j).support,
      2 ≤ successorDist u w) :
    NaryCompatible S := by
  refine ⟨?_, naryComponentMap_surjective S⟩
  rintro ⟨i, c⟩ ⟨j, d⟩ hcd
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  obtain ⟨y, rfl⟩ := Quotient.exists_rep d
  have hgen : Relation.EqvGen (inducedGraph successorGraph (narySupport S)).Rel
      ⟨x.1, Set.mem_iUnion.2 ⟨i, x.2⟩⟩ ⟨y.1, Set.mem_iUnion.2 ⟨j, y.2⟩⟩ :=
    Quotient.exact hcd
  obtain ⟨hy, hin⟩ := (eqvGen_within S hsep i _ _ hgen).1 x.2
  have hyi : y.1 ∈ (S i).support := hy
  have hij : i = j := by
    by_contra hne
    have hd := hsep i j hne _ hyi _ y.2
    have hs := successorDist_self y.1
    omega
  subst hij
  exact congrArg (fun z ↦ (⟨i, z⟩ : Σ k, (S k).Components)) (Quotient.sound hin)

/-! ## Neutral types, coordinates and cubes -/

/-- The sealed neutral-type object `NeutralType = {e₂, e₃-e₂} ⊆ Gr(M)`. -/
def NeutralType : Type :=
  {g : E289ProfileGroup // g = gradeGenerator ∨ g = defectGenerator - gradeGenerator}

/-- The two neutral generators are distinct. -/
theorem gradeGenerator_ne_defect : gradeGenerator ≠ defectGenerator - gradeGenerator := by
  intro h
  have hbt : (ternaryType : allowedComponentTypes) ≠ binaryType := by decide
  have hcon := congrArg (fun f : E289ProfileGroup ↦ f binaryType) h
  simp only [gradeGenerator, defectGenerator, Finsupp.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_apply, if_neg hbt] at hcon
  omega

/-- The neutral grade type `e₂`. -/
noncomputable def gradeType : NeutralType := ⟨gradeGenerator, Or.inl rfl⟩

/-- The neutral defect type `e₃ - e₂`. -/
noncomputable def defectType : NeutralType := ⟨defectGenerator - gradeGenerator, Or.inr rfl⟩

/-- The defining conditions of `NeutralCoordinate(α, b, c)`. -/
structure IsNeutralCoordinate (a : NeutralType) (bnd : ℚ) (c : PhysicalConstraint)
    (x : NeutralPair) : Prop where
  /-- The pair lies in the neutral fibre at `α`. -/
  profileDiff : x.profileDiff = a.1
  /-- The first alternative is `c`-admissible. -/
  admissible_fst : ConstraintAdmissible c x.fst
  /-- The second alternative is `c`-admissible. -/
  admissible_snd : ConstraintAdmissible c x.snd
  /-- The common resource value is below the prescribed bound. -/
  mass_lt : reciprocalValuePos x.fst < bnd
  /-- The first alternative lies in the binary stratum. -/
  stratum_fst : stateProfile x.fst = 2 • Finsupp.single binaryType 1
  /-- At the grade type the second alternative has profile `3e₂`. -/
  stratum_grade : a.1 = gradeGenerator →
    stateProfile x.snd = 3 • Finsupp.single binaryType 1
  /-- At the defect type the second alternative has profile `e₂ + e₃`. -/
  stratum_defect : a.1 = defectGenerator - gradeGenerator →
    stateProfile x.snd = Finsupp.single binaryType 1 + Finsupp.single ternaryType 1

/-- The neutral coordinate object `NeutralCoordinate(α, b, c)`. -/
def NeutralCoordinate (a : NeutralType) (bnd : ℚ) (c : PhysicalConstraint) : Type :=
  {x : NeutralPair // IsNeutralCoordinate a bnd c x}

/-- The complete two-alternative vertex footprint of a neutral pair. -/
def NeutralPair.footprint (x : NeutralPair) : Set successorGraph :=
  x.fst.support ∪ x.snd.support

theorem NeutralPair.footprint_finite (x : NeutralPair) : x.footprint.Finite :=
  (x.fst.support_finite).union (x.snd.support_finite)

/-- Weakening a neutral coordinate along a weaker physical constraint. -/
def NeutralCoordinate.mono {a : NeutralType} {bnd : ℚ} {c c' : PhysicalConstraint}
    (h : c ≤ c') (x : NeutralCoordinate a bnd c') : NeutralCoordinate a bnd c :=
  ⟨x.1, { x.2 with
    admissible_fst := constraintAdmissible_mono h x.2.admissible_fst
    admissible_snd := constraintAdmissible_mono h x.2.admissible_snd }⟩

/-- The finite neutral cube `NeutralCube(I, α, b, c)`: a tuple of neutral
coordinates whose every selector family factors through the direct `I`-ary
physical compatibility locus. -/
structure NeutralCube (I : Type) [Fintype I] (a : I → NeutralType) (bnd : I → ℚ)
    (c : PhysicalConstraint) where
  /-- The coordinates of the cube. -/
  coord : ∀ i, NeutralCoordinate (a i) (bnd i) c
  /-- Selectorwise direct `I`-ary compatibility. -/
  compatible : ∀ sigma : I → Bool,
    NaryCompatible fun i ↦ if sigma i then (coord i).1.snd else (coord i).1.fst

/-! ## The finite neutral cube is inhabited -/

/-- Every neutral coordinate object is inhabited, by the two sealed
certificates. -/
theorem exists_neutralCoordinate (a : NeutralType) (bnd : ℚ) (hbnd : 0 < bnd)
    (c : PhysicalConstraint) : Nonempty (NeutralCoordinate a bnd c) := by
  rcases a.2 with ha | ha
  · obtain ⟨z⟩ := (neutralFibres_remote_light c bnd hbnd).1
    refine ⟨⟨z.1.1, ?_⟩⟩
    exact
      { profileDiff := by rw [z.1.2, ha]
        admissible_fst := z.2.1.admissible_fst
        admissible_snd := z.2.1.admissible_snd
        mass_lt := by rw [coe_reciprocalValuePos]; exact z.2.1.mass_lt
        stratum_fst := z.2.2.1
        stratum_grade := fun _ ↦ z.2.2.2
        stratum_defect := fun hd ↦ absurd (ha.symm.trans hd) gradeGenerator_ne_defect }
  · obtain ⟨z⟩ := (neutralFibres_remote_light c bnd hbnd).2
    refine ⟨⟨z.1.1, ?_⟩⟩
    exact
      { profileDiff := by rw [z.1.2, ha]
        admissible_fst := z.2.1.admissible_fst
        admissible_snd := z.2.1.admissible_snd
        mass_lt := by rw [coe_reciprocalValuePos]; exact z.2.1.mass_lt
        stratum_fst := z.2.2.1
        stratum_grade := fun hg ↦ absurd (hg.symm.trans ha) gradeGenerator_ne_defect
        stratum_defect := fun _ ↦ z.2.2.2 }

/-- N.5: a finite tuple of neutral pairs, one in each prescribed coordinate
object, whose complete two-alternative footprints are pairwise separated. -/
private theorem exists_pairs :
    ∀ (n : ℕ) (a : Fin n → NeutralType) (bnd : Fin n → ℚ), (∀ i, 0 < bnd i) →
    ∀ c : PhysicalConstraint,
      ∃ x : Fin n → NeutralPair,
        (∀ i, IsNeutralCoordinate (a i) (bnd i) c (x i)) ∧
        ∀ i j : Fin n, i ≠ j → ∀ u ∈ (x i).footprint, ∀ w ∈ (x j).footprint,
          2 ≤ successorDist u w := by
  intro n
  induction n with
  | zero =>
      intro a bnd _ c
      exact ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
      intro a bnd hbnd c
      obtain ⟨x', hx'coord, hx'sep⟩ :=
        ih (fun i ↦ a i.castSucc) (fun i ↦ bnd i.castSucc) (fun i ↦ hbnd _) c
      letI : DecidableEq successorGraph.carrier := inferInstanceAs (DecidableEq ℕ+)
      have hEfin : (⋃ i : Fin n, (x' i).footprint).Finite :=
        Set.finite_iUnion fun i ↦ (x' i).footprint_finite
      set c' : PhysicalConstraint :=
        { forbidden := c.forbidden ∪ hEfin.toFinset
          margin := c.margin
          one_le_margin := c.one_le_margin } with hc'def
      have hcc' : c ≤ c' := ⟨Finset.subset_union_left, le_rfl⟩
      obtain ⟨z⟩ := exists_neutralCoordinate (a (Fin.last n)) (bnd (Fin.last n)) (hbnd _) c'
      have hlast : ∀ (i : Fin n), ∀ u ∈ (x' i).footprint, ∀ w ∈ z.1.footprint,
          2 ≤ successorDist u w := by
        intro i u hu w hw
        have hufb : u ∈ c'.forbidden :=
          Finset.mem_union_right _ (hEfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨i, hu⟩))
        have hadm : c'.margin < successorDist u w := by
          rcases hw with hw | hw
          · exact z.2.admissible_fst.1 u hufb w hw
          · exact z.2.admissible_snd.1 u hufb w hw
        have hm : 1 ≤ c'.margin := c'.one_le_margin
        omega
      refine ⟨Fin.lastCases z.1 x', ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last =>
            have hz : IsNeutralCoordinate (a (Fin.last n)) (bnd (Fin.last n)) c z.1 :=
              { z.2 with
                admissible_fst := constraintAdmissible_mono hcc' z.2.admissible_fst
                admissible_snd := constraintAdmissible_mono hcc' z.2.admissible_snd }
            simpa only [Fin.lastCases_last] using hz
        | cast i =>
            simpa only [Fin.lastCases_castSucc] using hx'coord i
      · intro i j
        induction i using Fin.lastCases with
        | last =>
            induction j using Fin.lastCases with
            | last => exact fun hij ↦ absurd rfl hij
            | cast j =>
                intro _ u hu w hw
                simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hu hw
                have hc := successorDist_comm w u
                have hd := hlast j w hw u hu
                omega
        | cast i =>
            induction j using Fin.lastCases with
            | last =>
                intro _ u hu w hw
                simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hu hw
                exact hlast i u hu w hw
            | cast j =>
                intro hij u hu w hw
                simp only [Fin.lastCases_castSucc] at hu hw
                exact hx'sep i j (fun h ↦ hij (congrArg Fin.castSucc h)) u hu w hw

/-- N.5: for every finite index object, every neutral-type map, every
coordinatewise positive rational bound and every finite physical constraint, the
finite neutral cube is inhabited — that is, its projection to the terminal
object is a regular epimorphism in the frozen `Type` setting. -/
theorem neutralCube_regularEpi (I : Type) [Fintype I] (a : I → NeutralType)
    (bnd : I → ℚ) (hbnd : ∀ i, 0 < bnd i) (c : PhysicalConstraint) :
    Nonempty (NeutralCube I a bnd c) := by
  classical
  set e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I with hedef
  obtain ⟨x, hxcoord, hxsep⟩ := exists_pairs (Fintype.card I) (fun k ↦ a (e.symm k))
    (fun k ↦ bnd (e.symm k)) (fun k ↦ hbnd _) c
  refine ⟨{ coord := fun i ↦ ⟨x (e i), ?_⟩, compatible := ?_ }⟩
  · have hi := hxcoord (e i)
    rwa [e.symm_apply_apply] at hi
  · intro sigma
    refine naryCompatible_of_separated _ ?_
    intro i j hij u hu w hw
    have hu' : u ∈ (x (e i)).footprint := by
      by_cases hs : sigma i
      · exact Or.inr (by simpa only [hs, if_true] using hu)
      · exact Or.inl (by simpa only [hs, if_false, Bool.false_eq_true] using hu)
    have hw' : w ∈ (x (e j)).footprint := by
      by_cases hs : sigma j
      · exact Or.inr (by simpa only [hs, if_true] using hw)
      · exact Or.inl (by simpa only [hs, if_false, Bool.false_eq_true] using hw)
    exact hxsep (e i) (e j) (fun h ↦ hij (e.injective h)) u hu' w hw'

end Erdos289
