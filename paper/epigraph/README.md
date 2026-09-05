# E289 epigraph proof workflow

This directory is deliberately local-first. The publication manuscript is not
changed while the display face is being selected.

## 1. Local TeX

macOS does not ship TeX. A current local TeX Live is sufficient for visual
iteration; the complete manuscript receives a separate final parity build
against arXiv's supported TeX Live 2025 environment.

The free-font specimen uses only fonts distributed by TeX Live:

- `cinzel`;
- `marcellus`;
- `cormorantgaramond`.

With BasicTeX, install them once:

```sh
sudo tlmgr install cinzel marcellus cormorantgaramond
```

No font binary needs to be downloaded, copied into the repository, or uploaded
to arXiv.

## 2. Render the comparison

Because this Mac currently has stale core LaTeX files in `~/Library/texmf`, run
the specimen with an empty `TEXMFHOME` so the TeX Live 2026 system tree remains
internally consistent:

```sh
cd paper/epigraph
mkdir -p /tmp/e289-empty-texmf
TEXMFHOME=/tmp/e289-empty-texmf \
  xelatex -interaction=nonstopmode -halt-on-error specimen.tex
open specimen.pdf
```

The sheet compares:

- Cinzel Regular and Bold;
- Marcellus Regular;
- Cormorant Garamond Medium and Semibold;
- no punctuation against full inscriptional interpuncts where most useful.

All candidates use the E306 control specification: 10.5/16 and `fontspec`
`LetterSpace=8`. Automatic font kerning remains enabled; no manual kerning or
synthetic bolding is used.

## 3. Publication choice

Cinzel is the closest first candidate: it was explicitly designed from
first-century Roman inscriptional proportions and is all-caps, while remaining
freely licensed. Marcellus gives a softer inscriptional alternative; Cormorant
Garamond is included as a more literary control rather than a Trajan substitute.

Once a family/weight/punctuation treatment is selected, the publication
manuscript can use the TeX Live font directly. There is then no proprietary-font
asset, no font upload, and no separate licensing workflow.

## 4. Build policy

- Fast local iteration: any current TeX Live installation is sufficient.
- Publication parity gate: rebuild the complete manuscript against arXiv's
  supported TeX Live 2025 environment before submission.
