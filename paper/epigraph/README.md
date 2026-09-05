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

## 3. Final publication asset

After one candidate is selected, generate one fixed-line PDF/vector asset on the
licensed desktop and commit only that generated asset.  Do **not** commit,
package, copy, or redistribute the Trajan font software.

Adobe Fonts expressly permits creating PDFs and vector artwork with activated
fonts, including converting type to outlines, and permits properly embedded font
data in PDFs for viewing/printing.  The intended publication source therefore
contains only the fixed generated output, never the font file.

## 4. Build policy

- Fast local iteration: any current TeX Live 2025 installation is sufficient.
- Publication parity gate: rebuild the complete manuscript in the arXiv-matched
  TeX Live 2025 snapshot dated 2025-08-03.

The exact snapshot is a seal/reproducibility condition, not a requirement for
every visual proof iteration.
