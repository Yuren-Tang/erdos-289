import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real

/-!
# Structural asymptotics

The filter-based and complete-lattice asymptotic interfaces used throughout
the E289 formalization.
-/

open Filter

namespace Erdos289

/-- The norm on `NNReal` fixed by U0.6: its underlying nonnegative real
value. Mathlib 4.33 supplies `NNNorm NNReal` but no `Norm NNReal` instance. -/
instance instNormNNReal : Norm NNReal where
  norm x := x

@[simp] theorem norm_nnreal (x : NNReal) : ‖x‖ = (x : ℝ) := rfl

/-- Mutual filter-based positive big-O. -/
def IsTheta {α E F : Type*} [Norm E] [Norm F] (l : Filter α)
    (f : α → E) (g : α → F) : Prop :=
  Asymptotics.IsTheta l f g

theorem isTheta_refl {α E : Type*} [Norm E] (l : Filter α) (f : α → E) :
    IsTheta l f f :=
  Asymptotics.isTheta_refl f l

theorem isTheta_symm {α E F : Type*} [Norm E] [Norm F] {l : Filter α}
    {f : α → E} {g : α → F} (h : IsTheta l f g) : IsTheta l g f :=
  Asymptotics.IsTheta.symm h

theorem isTheta_trans {α E F G : Type*} [Norm E] [SeminormedAddCommGroup F] [Norm G]
    {l : Filter α} {f : α → E} {g : α → F} {k : α → G}
    (hfg : IsTheta l f g) (hgk : IsTheta l g k) : IsTheta l f k :=
  Asymptotics.IsTheta.trans hfg hgk

theorem isTheta_congr {α E F : Type*} [Norm E] [Norm F] {l : Filter α}
    {f f' : α → E} {g g' : α → F} (h : IsTheta l f g)
    (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') : IsTheta l f' g' :=
  hf.symm.trans_isTheta (Asymptotics.IsTheta.trans_eventuallyEq h hg)

theorem isTheta_mono_filter {α E F : Type*} [Norm E] [Norm F]
    {l l' : Filter α} {f : α → E} {g : α → F} (h : IsTheta l f g)
    (hl : l' ≤ l) : IsTheta l' f g :=
  Asymptotics.IsTheta.mono h hl

/-- The pointwise supremum over every parameter. -/
def UniformSup {P α L : Type*} [CompleteLattice L] (u : P → α → L) : α → L :=
  fun a ↦ ⨆ p, u p a

theorem uniformSup_le_iff {P α L : Type*} [CompleteLattice L]
    (u : P → α → L) (h : α → L) (a : α) :
    UniformSup u a ≤ h a ↔ ∀ p, u p a ≤ h a := by
  simp [UniformSup]

/-- The canonical grade filter. -/
def GradeFilter : Filter ℕ := atTop

theorem gradeFilter_neBot : GradeFilter.NeBot := by
  rw [GradeFilter]
  infer_instance

/-- Epsilon-domination little-o for extended nonnegative values. -/
def ENNRealLittleO {α : Type*} (l : Filter α) (f g : α → ENNReal) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ a in l, f a ≤ ENNReal.ofReal c * g a

namespace ENNRealLittleO

theorem congr {α : Type*} {l : Filter α} {f f' g g' : α → ENNReal}
    (h : ENNRealLittleO l f g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
    ENNRealLittleO l f' g' := by
  intro c hc
  filter_upwards [h c hc, hf, hg] with a ha hfa hga
  simpa [← hfa, ← hga] using ha

theorem mono_left {α : Type*} {l : Filter α} {f f' g : α → ENNReal}
    (hff' : f' ≤ᶠ[l] f) (h : ENNRealLittleO l f g) : ENNRealLittleO l f' g := by
  intro c hc
  filter_upwards [hff', h c hc] with a hle ho
  exact hle.trans ho

theorem mono_right {α : Type*} {l : Filter α} {f g g' : α → ENNReal}
    (h : ENNRealLittleO l f g) (hgg' : g ≤ᶠ[l] g') : ENNRealLittleO l f g' := by
  intro c hc
  filter_upwards [h c hc, hgg'] with a ho hle
  exact ho.trans (by simpa [mul_comm] using mul_le_mul_left hle (ENNReal.ofReal c))

theorem mono_filter {α : Type*} {l l' : Filter α} {f g : α → ENNReal}
    (h : ENNRealLittleO l f g) (hl : l' ≤ l) : ENNRealLittleO l' f g := by
  intro c hc
  exact hl (h c hc)

end ENNRealLittleO

/-- Uniform epsilon-domination with the parameter quantifier inside one
eventual statement. -/
def UniformLittleO {P α : Type*} (l : Filter α) (u : P → α → ENNReal)
    (g : α → ENNReal) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ᶠ a in l, ∀ p, u p a ≤ ENNReal.ofReal c * g a

theorem uniformLittleO_iff_uniformSup {P α : Type*} {l : Filter α}
    {u : P → α → ENNReal} {g : α → ENNReal} :
    UniformLittleO l u g ↔ ENNRealLittleO l (UniformSup u) g := by
  constructor
  · intro h c hc
    filter_upwards [h c hc] with a ha
    exact (uniformSup_le_iff u (fun a ↦ ENNReal.ofReal c * g a) a).2 ha
  · intro h c hc
    filter_upwards [h c hc] with a ha
    exact fun p ↦ (le_iSup (fun p ↦ u p a) p).trans ha

theorem nnreal_isLittleO_iff_ennrealLittleO {α : Type*} {l : Filter α}
    {f g : α → NNReal} :
    Asymptotics.IsLittleO l f g ↔
      ENNRealLittleO l (fun a ↦ (f a : ENNReal)) (fun a ↦ (g a : ENNReal)) := by
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro h c hc
    filter_upwards [h hc] with a ha
    have hreal : (f a : ℝ) ≤ c * (g a : ℝ) := by simpa using ha
    simpa [ENNReal.ofReal_mul hc.le] using ENNReal.ofReal_le_ofReal hreal
  · intro h c hc
    filter_upwards [h c hc] with a ha
    have hofReal : ENNReal.ofReal (f a : ℝ) ≤
        ENNReal.ofReal (c * (g a : ℝ)) := by
      simpa [ENNReal.ofReal_mul hc.le] using ha
    have hreal : (f a : ℝ) ≤ c * (g a : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc.le (g a).coe_nonneg)).mp hofReal
    simpa using hreal

end Erdos289

