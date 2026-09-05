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

`specimen.tex` is only a glyph-level reference. It is useful for seeing the
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

## 3. What the E306 baseline actually is

Do not conflate the current E289 manuscript setting with E306.

The current successful E306 manuscript uses, for its Greek dedication:

- Gentium Book Medium;
- 10.5 pt on 16 pt;
- `fontspec` `LetterSpace=9`;
- 8 pt / 12 pt vertical spacing.

In `fontspec`, `LetterSpace=9` means an additive 9% of the font size between
letters, i.e. 0.09 em. This is a useful optical starting point for an all-caps
display line, not a universal typographic law.

An earlier accepted E306 checkpoint used Artemisia at 10/15 with no added
tracking. Therefore there is no timeless rule "E306 = 0.08 em".

The 0.08 em value belongs instead to the **current E289 manuscript**, where the
TeX Live Trajan line is defined through `soul`/`\sodef`.

## 4. Phase-I decision gate: real first-page context

The actual family/weight decision is made with `context-specimen.tex`. This is
a controlled copy of the real E289 first-page environment: the same `amsart`
class, ETbb text face, NewTX mathematics, title, author, ORCID, abstract, and the
actual beginning of the Introduction. The publication manuscript itself is not
modified.

For the normalized family/weight gate, freeze:

- the E289 Latin wording and comma:
  `CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO`;
- E306-current geometry: 10.5/16 and 8 pt / 12 pt vertical spacing;
- E306-current tracking target: 0.09 em / `LetterSpace=9`;
- normal OpenType kerning for OpenType candidates;
- no manual kerning and no synthetic emboldening.

Only **family and weight** vary inside the normalized gate.

Build with:

```sh
cd paper/epigraph
sh build-context.sh
open context-*.pdf
```

`build-context.sh` performs a preflight and prints the exact `tlmgr install`
command if this BasicTeX installation lacks a manuscript or proof dependency.

The seven proofs are:

1. `context-00-trajan-current-08.pdf` — historical E289-current Trajan at
   0.08 em; reference only, not part of the normalized gate;
2. `context-01-trajan-normalized-09.pdf` — the same Trajan family normalized
   to the E306-current 0.09 em tracking target;
3. `context-02-cinzel-regular.pdf`;
4. `context-03-cinzel-bold.pdf`;
5. `context-04-marcellus-regular.pdf`;
6. `context-05-cormorant-medium.pdf`;
7. `context-06-cormorant-semibold.pdf`.

Thus variants 1--6 are directly comparable at the same tracking target, while
variant 0 records what the present E289 manuscript actually does.

### Trajan reference implementation

The TeX Live `trajan` family is a legacy Type 1/METAFONT font. Rather than force
it through XeTeX, `build-context.sh` renders two tiny reference PDFs with
pdfLaTeX+soul and embeds them at natural size into the XeLaTeX first-page proof.

The tracked text is deliberately written **literally** inside the `soul`
command. Passing the whole line through an unregistered macro can make soul's
reconstruction pass fail with `Reconstruction failed`, even under pdfLaTeX.
This was the cause of the previous failed control build; it was not evidence
that 0.08 em itself or the Trajan font was invalid.

Judge the **whole first page**, not the epigraph line in isolation: optical
weight against the title, line width, relation to the ETbb page texture, and
whether the epigraph reads as part of the title matter rather than as a separate
decoration.

## 5. Phase II: local optical tuning

Only the Phase-I survivors should be tuned further. Start from the E306-current
0.09 em gate, but treat that value as a prior rather than a rule. Vary one
parameter at a time:

1. punctuation treatment (comma versus inscriptional interpuncts or none);
2. small tracking adjustments around 9;
3. only if necessary, a small weight or size adjustment;
4. vertical spacing last.

A family may legitimately prefer less or more tracking than E306 because its
native sidebearings, cap proportions and weight are different. The purpose of
Phase I is merely to avoid confounding family choice with simultaneous optical
tuning.

## 6. Publication choice

Cinzel is the closest free first candidate: it was explicitly designed from
first-century Roman inscriptional proportions and is all-caps. Marcellus gives
a softer inscriptional alternative; Cormorant Garamond is included as a more
literary control rather than a Trajan substitute. These are priors only: the
real-page Phase-I proof decides.

Once a family/weight/punctuation treatment is selected, the publication
manuscript can use the TeX Live font directly.

## 7. Build policy

- Fast local iteration: any current TeX Live installation is sufficient.
- Publication parity gate: rebuild the complete manuscript against arXiv's
  supported TeX Live 2025 environment before submission.
