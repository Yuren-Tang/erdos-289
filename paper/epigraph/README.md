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
These, rather than an earlier/later E306 typography branch tip, are the baseline
geometry. Commit `9ab332be...` is useful ancestry for the EB Garamond selection
but is not itself the exact frozen manuscript object.

## 2. Phase I: family / weight gate

`context-specimen.tex` reproduces the real E289 first-page environment: `amsart`,
ETbb body text, NewTX mathematics, title, author, ORCID, abstract, and the actual
beginning of the Introduction.

Phase I froze the Latin wording and comma, 10.5/16, `LetterSpace=8`, 8 pt / 12 pt
vertical spacing, ordinary kerning, and no synthetic emboldening. The six complete
first-page proofs compared EB Garamond Medium, Cinzel Regular/Bold, Marcellus
Regular, and Cormorant Garamond Medium/Semibold.

The Owner's optical assessment made EB Garamond Medium the clear leader. The
useful failure specimen was Cormorant Medium: promising Trajan-like proportions,
but too fine; Semibold restored weight at the cost of excessive modern
thick/thin contrast. Cinzel Regular was too weak, Cinzel Bold somewhat rigid,
and Marcellus stylistically farther from the intended register.

## 3. Phase I.5: weight versus tracking

`build-phase15.sh` varied only EB Garamond weight and tracking. Medium was tested
at 8/9/10/11; Regular at 8/9. The Regular cut remained too fine at this page
scale, so the weight dimension was closed at **EB Garamond Medium**. Medium 8 was
slightly tight, 11 slightly loose, with the useful region around 9--10.

## 4. Phase I.6: blind fine-tracking gate

`build-phase16.sh` reproducibly builds EB Garamond Medium at LetterSpace 8.5,
9.0, 9.5 and 10.0. The judgement packet used six concealed pages, duplicating
9.0 and 9.5.

Blind result:

- 8.5 was judged slightly constrained;
- 10.0 slightly loose;
- the 9.0--9.5 region was the stable sweet spot;
- the two 9.5 copies were correctly recognized as identical;
- the two 9.0 copies nevertheless received somewhat different momentary
  impressions, providing a useful estimate of perceptual/order noise;
- across Phase I.5 and I.6 the Owner showed a small but repeated preference for
  9.0 as the more exact/collected setting over 9.5 as slightly looser.

Accordingly the provisional optical setting is now closed at:

```text
family/weight  EB Garamond Medium
LetterSpace    9
size/leading   10.5 / 16
vertical       8 pt before / 12 pt after
```

This does not claim that a hypothetical mathematical optimum is exactly 9.000;
it is the robust representative of a visually indistinguishable 9--9.5 band and
avoids overfitting sub-unit tracking differences.

## 5. Phase I.7: blind punctuation gate

`build-phase17.sh` keeps the provisional setting above fixed and varies only the
punctuation treatment:

1. `CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO`;
2. `CARPE DIEM QVAM MINIMVM CREDVLA POSTERO`;
3. `CARPE · DIEM · QVAM · MINIMVM · CREDVLA · POSTERO`.

The six-page judgement packet contains each candidate twice in concealed
randomized order. The page-to-punctuation key is deliberately not recorded in
repository history before judgement. See `PHASE17_BLIND_PROTOCOL.md`.

The point of this gate is not merely "which looks most Roman". The comma retains
the literary/editorial syntax of the Horatian quotation; the no-punctuation form
lets the all-cap spacing carry the pause; the interpunct form deliberately tests
a more inscriptional presentation and may fail if it reads as theatrical
pseudo-antique styling rather than a restrained mathematical dedication.

## 6. Local build and remote parity

Local builds are the normal iteration path and have been demonstrated to work
without the legacy Trajan chain. Because the Owner's Mac has stale files in
`~/Library/texmf`, the scripts use an empty temporary `TEXMFHOME` by default.

```sh
cd paper/epigraph
sh build-phase17.sh
```

`.github/workflows/epigraph-context.yml` is retained only as a manual
`workflow_dispatch` TeX Live 2025/arXiv-parity utility. It does not block optical
iteration.

Legacy TeX-Live Trajan remains outside the decision gate: repairing its old
Type-1/map/PK fallback chain would add environment noise without improving this
OpenType comparison.

## 7. Publication boundary

No experiment here changes `paper/manuscript.tex`. After punctuation is chosen,
perform one final whole-page optical check before a separate bounded manuscript
change and the ordinary full-manuscript TeX Live/arXiv parity gates.
