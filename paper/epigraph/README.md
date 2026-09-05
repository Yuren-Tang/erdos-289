# E289 epigraph proof workflow

This directory is an isolated typography experiment. The publication manuscript
is not changed while the epigraph display face is being selected.

## 1. Exact E306 reference

The Owner-specified reference is the exact frozen E306 arXiv-v1 source object,
not whichever E306 branch happens to be current later.

Frozen provenance:

```text
source ZIP
sha256 2856963cfab075e1c888212e1960a071922faa69119c42384e14248a9213b85e

reference PDF
sha256 7a2b44ef2410312fbd7db2fbd70727c705edf463772e55c208ac0c7c2948653c
pages 35 A4

main.tex inside the frozen source ZIP
sha256 11570a165e963f113c0ea00bd1bc95bbe1e52f449c8d3fafda4d0d1b082ee56a
```

The exact frozen `main.tex` declares:

```tex
\newfontfamily\greekdedicationfont{EBGaramond-Medium.otf}[
  ItalicFont=EBGaramond-Medium.otf,
  LetterSpace=8
]
```

and sets the dedication at 10.5 pt on 16 pt with 8 pt before and 12 pt after.
These, rather than an earlier/later E306 typography branch tip, are the Phase-I
baseline parameters. Commit `9ab332be...` is useful ancestry for the EB Garamond
selection but is not itself the exact frozen manuscript object.

## 2. Phase-I gate: real E289 first-page context

`context-specimen.tex` reproduces the real E289 first-page environment: `amsart`,
ETbb body text, NewTX mathematics, title, author, ORCID, abstract, and the actual
beginning of the Introduction. Only the epigraph family/weight varies.

Phase I freezes:

- `CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO` including the comma;
- 10.5/16;
- `LetterSpace=8`;
- 8 pt / 12 pt vertical spacing;
- ordinary font kerning, no hand kerning, no synthetic emboldening.

The six complete first-page proofs are:

1. `context-00-e306-ebgaramond-medium.pdf` — exact E306 family/weight control,
   with the E289 Latin line;
2. `context-01-cinzel-regular.pdf`;
3. `context-02-cinzel-bold.pdf`;
4. `context-03-marcellus-regular.pdf`;
5. `context-04-cormorant-medium.pdf`;
6. `context-05-cormorant-semibold.pdf`.

Judge the whole first page: optical weight against the title, line width, relation
to the ETbb page texture, and whether the epigraph belongs to the title matter
rather than reading as a detached ornament.

A local full-TeX-Live build on 2026-09-05 successfully generated all six A4
proofs. Initial optical triage retained EB Garamond Medium, Cinzel Regular and
Marcellus Regular; Cinzel Bold was too dark against the title, Cormorant Medium
too light, and Cormorant Semibold remained more literary/calligraphic than the
leading inscriptional candidates. This is a working shortlist, not a publication
selection.

Legacy TeX-Live Trajan is deliberately **not** part of this gate. On a minimal
BasicTeX installation its Type-1/map/PK fallback chain can require additional
legacy utilities such as `gsftopk`; making that environment repair a prerequisite
for choosing an OpenType display face adds no useful information. The old
`trajan-control-asset.tex` is retained only as historical experiment material.

## 3. Local build

The build script performs a preflight and prints the exact missing TeX-Live
packages. After dependencies are present:

```sh
cd paper/epigraph
sh build-context.sh
open context-*.pdf
```

Because the Owner's Mac has stale files in `~/Library/texmf`, `build-context.sh`
uses an empty temporary `TEXMFHOME` by default.

The glyph-level `specimen.tex` remains available as a secondary reference, but
it is not a decision gate because it lacks page context.

Local builds are the normal iteration path. They have now been demonstrated to
work without the legacy Trajan chain.

## 4. Remote parity build

`.github/workflows/epigraph-context.yml` is retained only as a manual
`workflow_dispatch` TeX Live 2025/arXiv-parity utility. It no longer runs on every
specimen change and therefore does not block optical iteration with irrelevant
CI status.

## 5. Phase II

Only Phase-I survivors are tuned further. Keep the frozen E306 values as the
starting point, then vary one parameter at a time:

1. punctuation treatment;
2. small tracking changes around 8;
3. weight or size only if still necessary;
4. vertical spacing last.

The working Phase-I survivors are:

- EB Garamond Medium — exact E306 family/weight control, highly integrated with
  the mathematical page but less explicitly inscriptional;
- Cinzel Regular — strongest monumental/inscriptional candidate without the
  excessive blackness of Cinzel Bold;
- Marcellus Regular — softer inscriptional alternative.

Different families may have different eventual optimal tracking because their
native sidebearings and cap proportions differ. Phase I fixes the value only to
make the family/weight comparison identifiable.

## 6. Publication boundary

No experiment here changes `paper/manuscript.tex`. After a display face and its
optical parameters are chosen, the publication manuscript receives a separate
bounded typography change and the ordinary full-manuscript TeX Live/arXiv parity
gates.
