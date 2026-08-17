# affine-correction 0.2.0

Lean 4 / mathlib formalization of the universal graded affine-correction core.

This version implements the final categorical interface rather than the older
homogeneous-family corollary:

- a Set-level partial physical commutative monoid;
- a genuine coherent observation functor `Q : I ⥤ Ab` and natural observation
  transformation;
- correction **and grade in one category** (the strict one-object-fibre normal
  form of `∫ B(UQ × M)`);
- required graded correction fibres;
- realizer pullbacks;
- coverage as surjectivity of the pullback projection;
- minimal physical composition as one surjectivity statement from compatible
  realizer pairs to the composite fibre;
- target-realizer pullback and exact-fibre transfer.

The public core intentionally contains **no** `Homogeneous` predicate and no
whole-family `FullyCompatible` hypothesis.

## Toolchain

Pinned to Lean / mathlib `v4.33.0` (final release).

```bash
lake update
lake exe cache get
lake build
```

## Status

The mathematical interface has been statically audited against the final E289
categorical baseline and checked against the Lean 4.33.0 release notes and the
mathlib `v4.33.0` API surface used by this package. The generation container has
no Lean toolchain, so this archive has not been mechanically built there. Treat
it as a build candidate until `lake build` is run in a Lean-enabled environment.


## v0.2.0-r2 (Lean 4.33.0 compatibility)

This revision makes the definitional equality in `Realizer.transition_observation_eq_label` explicit with `change` before rewriting. It changes no mathematical statement or public categorical interface.
