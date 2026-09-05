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
sudo tlmgr update --self
sudo tlmgr install cinzel marcellus cormorantgaramond
```

No font binary needs to be downloaded, copied into the repository, or uploaded
to arXiv.

## 2. Glyph-level reference sheet

`specimen.tex` is only a glyph-level reference.  It is useful for seeing the
families and weights in isolation, but it is **not** the publication decision
gate because it contains no real first-page context.

Because this Mac currently has stale core LaTeX files in `~/Library/texmf`, run
it with an empty `TEXMFHOME` so the TeX Live 2026 system tree remains internally
consistent:

```sh
cd paper/epigraph
mkdir -p /tmp/e289-empty-texmf
TEXMFHOME=/tmp/e289-empty-texmf \
  xelatex -interaction=nonstopmode -halt-on-error specimen.tex
open specimen.pdf
```

The sheet compares Cinzel Regular/Bold, Marcellus Regular, and Cormorant
Garamond Medium/Semibold, with punctuation variants where useful.

## 3. Phase-I decision gate: real first-page context

The actual family/weight decision is made with `context-specimen.tex`.  This is
a controlled copy of the real E289 first-page environment: the same `amsart`
class, ETbb text face, NewTX mathematics, title, author, ORCID, abstract, and the
actual beginning of the Introduction.  The publication manuscript itself is
not modified.

Phase I freezes the successful E306/current-manuscript parameters:

- exact wording and comma: `CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO`;
- 10.5 pt on 16 pt;
- tracking 8 (the Trajan control retains the manuscript's exact `soul` setup);
- existing 8 pt / 12 pt vertical spacing;
- normal OpenType kerning, no manual kerning, no synthetic emboldening.

Only **family and weight** vary.  Build the complete matrix with:

```sh
cd paper/epigraph
sh build-context.sh
open context-*.pdf
```

The six proofs are:

1. `context-00-trajan-control.pdf` — exact current manuscript control;
2. `context-01-cinzel-regular.pdf`;
3. `context-02-cinzel-bold.pdf`;
4. `context-03-marcellus-regular.pdf`;
5. `context-04-cormorant-medium.pdf`;
6. `context-05-cormorant-semibold.pdf`.

Judge the **whole first page**, not the epigraph line in isolation: optical
weight against the title, line width, relation to the ETbb page texture, and
whether the epigraph reads as part of the title matter rather than as a separate
decoration.  Do not tune punctuation, tracking, size, or vertical spacing until
a family/weight shortlist survives this gate.

## 4. Phase II: local optical tuning

Only the Phase-I survivors should be tested further.  Starting from the frozen
E306 control, vary one optical parameter at a time, in this order unless the
page gives a strong reason otherwise:

1. punctuation treatment (comma versus inscriptional interpuncts or none);
2. small tracking adjustments around 8;
3. only if still necessary, a small weight or size adjustment;
4. vertical spacing last.

This keeps the experiment identifiable: a rejected page should have a clear
reason rather than several simultaneous changes.

## 5. Publication choice

Cinzel is the closest free first candidate: it was explicitly designed from
first-century Roman inscriptional proportions and is all-caps. Marcellus gives
a softer inscriptional alternative; Cormorant Garamond is included as a more
literary control rather than a Trajan substitute.  These are priors only: the
real-page Phase-I proof decides.

Once a family/weight/punctuation treatment is selected, the publication
manuscript can use the TeX Live font directly. There is then no proprietary-font
asset, no font upload, and no separate licensing workflow.

## 6. Build policy

- Fast local iteration: any current TeX Live installation is sufficient.
- Publication parity gate: rebuild the complete manuscript against arXiv's
  supported TeX Live 2025 environment before submission.
