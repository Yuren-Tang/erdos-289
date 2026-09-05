# E289 epigraph proof workflow

This directory is deliberately local-first.  The publication manuscript is not
changed while the display face is being selected.

## 1. Activate the licensed font

Activate **Trajan** in Adobe Fonts on the local Mac.  The specimen expects the
desktop family exposed as `Trajan Pro 3`, with `Regular` and `Semibold` styles.
No Adobe font file belongs in this repository.

## 2. Render the four-way proof

From `paper/epigraph/`:

```sh
latexmk -xelatex -interaction=nonstopmode -halt-on-error specimen.tex
open specimen.pdf
```

The four candidates differ only in:

- Regular vs Semibold;
- no punctuation vs inscriptional interpuncts.

All use 10.5/16 and `fontspec` `LetterSpace=8`.  Kerning is not disabled or
manually altered.  No synthetic bolding is used.

## 3. Generate the selected fixed-line asset

`asset.tex` produces a tightly cropped one-line PDF at the final 10.5 pt size.
The two switches are supplied on the XeLaTeX command line.

Regular, no punctuation:

```sh
xelatex -jobname=epigraph-final asset.tex
```

Regular, interpuncts:

```sh
xelatex -jobname=epigraph-final '\def\EpigraphInterpuncts{1}\input{asset.tex}'
```

Semibold, no punctuation:

```sh
xelatex -jobname=epigraph-final '\def\EpigraphSemibold{1}\input{asset.tex}'
```

Semibold, interpuncts:

```sh
xelatex -jobname=epigraph-final '\def\EpigraphSemibold{1}\def\EpigraphInterpuncts{1}\input{asset.tex}'
```

The generated `epigraph-final.pdf` is the only Trajan-bearing publication asset
that needs to be committed.  A properly subset-embedded PDF is already within
Adobe Fonts' stated PDF embedding permission, so converting the line to outlines
is optional rather than required.  Outlining may still be used if we want the
asset to contain no embedded font program at all.

Do **not** commit, package, copy, or redistribute the Trajan font software itself.

## 4. Build policy

- Fast local iteration: any current TeX Live 2025 installation is sufficient.
- Publication parity gate: rebuild the complete manuscript in the arXiv-matched
  TeX Live 2025 snapshot dated 2025-08-03.

The exact snapshot is a seal/reproducibility condition, not a requirement for
every visual proof iteration.
