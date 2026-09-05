# Erdős 289 publication manuscript

This directory contains the publication-facing manuscript for the ordinary Erdős Problem 289 result, in the stronger subsystem where every connected component has length 2 or 3.

## Active manuscript

The TeX root is `main.tex`. The active mathematical source is:

- `sections/00-introduction.tex`
- `sections/01-states-and-filtration.tex`
- `sections/02-auxiliary-inputs.tex`
- `sections/03-signed-inverse.tex`
- `sections/04-wide-start.tex`
- `sections/05-local-profile.tex`
- `sections/06-scalar-finality.tex`
- `sections/07-finite-realization.tex`
- `sections/08-terminalization.tex`
- `appendices/prime-supply.tex`
- `appendices/restricted-fold.tex`
- `appendices/prefix-seed.tex`

The finite certificate displayed in Appendix C is replayed by `tools/verify_prefix_seed.py` using exact rational arithmetic.

## Proof architecture

The proof has four layers.

1. Signed-inverse interval families control the successive prime-power quotients of `Q/Z` with bounded incompatibility and summable reciprocal cost.
2. Reciprocal-neutral Boolean switches widen the available component-count interval without changing residue and with arbitrarily small additional reciprocal cost.
3. A uniform restricted-sum transfer reduces the construction to scalar width dynamics: gains at prime stages dominate the accumulated losses at composite prime powers.
4. After a finite terminal cutoff is fixed, Haxell thinning supplies literal joint compatibility. The labelled-relation calculus then strictifies the local observable transfers, and a terminal pullback at residue zero gives the exact reciprocal sum `1`.

The categorical layer records one specific distinction: observable relations can compose even when their concrete interval labels are not jointly compatible. The oplax comparison records this loss; the finite compatibility theorem makes the comparison an identity.

## Verification

The manuscript is built in the fixed TeX Live 2025-08-03 full snapshot. CI checks the active-source label/reference graph, replays the finite initialization, builds with XeLaTeX/Biber, rejects missing glyphs and overfull boxes, rejects Type 3 fonts, and uploads the publication PDF.

Complete Lean formalization is a separate project and is not a dependency of the human-paper publication build.

## Historical material

Other files and directories in the paper workbench record earlier proof architectures, audits, or typography experiments. They are not referenced by `main.tex` and are not part of the public manuscript source package.
