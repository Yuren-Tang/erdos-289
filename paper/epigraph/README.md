# E289 epigraph proof workflow

This directory is deliberately local-first. The publication manuscript is not
changed while the display face is being selected.

## 1. Local TeX

macOS does not ship a TeX distribution. For this specimen, full MacTeX is not
needed: BasicTeX is sufficient because it includes XeTeX. A current local TeX
Live release is fine for visual iteration; the complete manuscript receives a
separate final parity build against the arXiv TeX Live 2025 environment.

The specimen itself needs only XeLaTeX + `fontspec`; `latexmk` is not required.

## 2. Activate Trajan

Trajan is not a macOS system font. Activate the **Trajan** family from Adobe
Fonts through the Creative Cloud desktop app. The Adobe family contains the
Trajan Pro 3 weights, including Regular and Semibold. No Adobe font file belongs
in this repository.

After activation, restart Terminal if necessary and confirm that the family is
visible in Font Book / desktop applications.

## 3. Render the four-way proof

The specimen lives in this directory, not at the repository root:

```sh
cd paper/epigraph
xelatex -interaction=nonstopmode -halt-on-error specimen.tex
open specimen.pdf
```

The four candidates differ only in:

- Regular vs Semibold;
- no punctuation vs inscriptional interpuncts.

All use 10.5/16 and `fontspec` `LetterSpace=8`. Kerning is not disabled or
manually altered. No synthetic bolding is used.

## 4. Generate the selected fixed-line asset

`asset.tex` produces a tightly cropped one-line PDF at the final 10.5 pt size.
The generated `epigraph-final.pdf` is the only Trajan-bearing publication asset
that needs to be committed. Do not commit, package, copy, or redistribute the
Trajan font software itself.

## 5. Build policy

- Fast local iteration: any current TeX Live installation is sufficient.
- Publication parity gate: rebuild the complete manuscript against arXiv's
  supported TeX Live 2025 environment before submission.

The exact arXiv package snapshot is a seal/reproducibility condition, not a
requirement for every visual proof iteration.
