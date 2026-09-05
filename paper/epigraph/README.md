# E289 epigraph proof workflow

This directory is an isolated typography experiment. The publication manuscript
is not changed while the epigraph display face is being selected.

## 1. Exact E306 reference

The Owner-specified reference is the E306 EB-Garamond finalization, not whichever
E306 branch happens to be current later.

Traceable source:

```text
repository: Yuren-Tang/erdos-306
branch:     finalization/e306-ebgaramond-v1
commit:     9ab332be9e02248f603b718a4c918e36d595a50b
message:    Select EB Garamond Medium dedication for arXiv v1
```

Its dedication declaration is:

```tex
\newfontfamily\greekdedicationfont{EBGaramond-Medium.otf}[
  ItalicFont=EBGaramond-Medium.otf,
  LetterSpace=8
]
```

and its title-matter geometry is 10.5 pt on 16 pt with 8 pt before and 12 pt
after the dedication. These are the Phase-I baseline parameters.

This corrects two historical confusions in earlier experiments: `LetterSpace=9`
belongs to a later STIX/Gentium E306 finalization, while 0.08 em Trajan tracking
belongs to the then-current E289 manuscript. Neither supersedes the Owner's
specified E306 reference above.

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

Because this Mac has stale files in `~/Library/texmf`, `build-context.sh` uses an
empty temporary `TEXMFHOME` by default.

The glyph-level `specimen.tex` remains available as a secondary reference, but
it is not a decision gate because it lacks page context.

## 4. Authoritative remote build

`.github/workflows/epigraph-context.yml` builds the same six proofs inside the
repository's established full TeX Live 2025-08-03 snapshot and uploads them as a
single artifact. It runs on changes to this experiment branch and can also be
started manually.

The remote build is the stable comparison surface. Local BasicTeX is only a
convenience for rapid inspection and need not reproduce obsolete Type-1 Trajan
machinery.

## 5. Phase II

Only Phase-I survivors are tuned further. Keep the E306 values as the starting
point, then vary one parameter at a time:

1. punctuation treatment;
2. small tracking changes around 8;
3. weight or size only if still necessary;
4. vertical spacing last.

Different families may have different eventual optimal tracking because their
native sidebearings and cap proportions differ. Phase I fixes the value only to
make the family/weight comparison identifiable.

## 6. Publication boundary

No experiment here changes `paper/manuscript.tex`. After a display face and its
optical parameters are chosen, the publication manuscript receives a separate
bounded typography change and the ordinary full-manuscript TeX Live/arXiv parity
gates.
