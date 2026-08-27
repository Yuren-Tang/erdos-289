import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Invariant affine-fibre extension

The coordinate-free sum of a complete affine `H`-fibre with a complete
`K/H`-fibre modulo `H`.
-/

open Set
open scoped Pointwise

namespace Erdos289

/-- If `f` fills one affine `H`-fibre and `g` fills one affine `K/H`-fibre
modulo `H`, their product-family sum fills the corresponding affine `K`-fibre. -/
theorem affineFiber_add {A X Y : Type*} [AddCommGroup A]
    (H K : AddSubgroup A) (hHK : H ≤ K) (f : X → A) (g : Y → A) (x y : A)
    (hf : Set.range f = ({x} : Set A) + (H : Set A))
    (hg : Set.range g + (H : Set A) = ({y} : Set A) + (K : Set A)) :
    Set.range (fun uv : X × Y ↦ f uv.1 + g uv.2) =
      ({x + y} : Set A) + (K : Set A) := by
  ext z
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    have hfu : f u ∈ ({x} : Set A) + (H : Set A) := hf ▸ Set.mem_range_self u
    rcases Set.mem_add.mp hfu with ⟨x', hx', h, hh, hsum⟩
    have hx' : x' = x := Set.mem_singleton_iff.mp hx'
    subst x'
    have hgvH : g v ∈ Set.range g + (H : Set A) := by
      simpa using Set.add_mem_add (Set.mem_range_self v) H.zero_mem
    have hgvK : g v ∈ ({y} : Set A) + (K : Set A) := hg ▸ hgvH
    rcases Set.mem_add.mp hgvK with ⟨y', hy', k, hk, gsum⟩
    have hy' : y' = y := Set.mem_singleton_iff.mp hy'
    subst y'
    apply Set.mem_add.mpr
    refine ⟨x + y, Set.mem_singleton _, h + k, K.add_mem (hHK hh) hk, ?_⟩
    change x + y + (h + k) = f u + g v
    rw [← hsum, ← gsum]
    ac_rfl
  · intro hz
    rcases Set.mem_add.mp hz with ⟨xy, hxy, k, hk, rfl⟩
    have hxy : xy = x + y := Set.mem_singleton_iff.mp hxy
    subst xy
    have hyk : y + k ∈ ({y} : Set A) + (K : Set A) :=
      Set.add_mem_add (Set.mem_singleton y) hk
    have hyk' : y + k ∈ Set.range g + (H : Set A) := hg.symm ▸ hyk
    rcases Set.mem_add.mp hyk' with ⟨gv, hgv, h, hh, gh_eq⟩
    rcases hgv with ⟨v, rfl⟩
    have hxh : x + h ∈ ({x} : Set A) + (H : Set A) :=
      Set.add_mem_add (Set.mem_singleton x) hh
    have hxh' : x + h ∈ Set.range f := hf.symm ▸ hxh
    rcases hxh' with ⟨u, fu_eq⟩
    refine ⟨(u, v), ?_⟩
    dsimp
    rw [fu_eq]
    calc
      x + h + g v = x + (g v + h) := by ac_rfl
      _ = x + (y + k) := congrArg (x + ·) gh_eq
      _ = x + y + k := by ac_rfl

end Erdos289

