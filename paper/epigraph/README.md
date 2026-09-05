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

## 3. Phase I.5--I.6: weight and tracking

`build-phase15.sh` varied only EB Garamond weight and tracking. The Regular cut
remained too fine at this page scale, so the weight dimension closed at **EB
Garamond Medium**. Medium 8 was slightly tight, 11 slightly loose, with the useful
region around 9--10.

`build-phase16.sh` then tested Medium at LetterSpace 8.5, 9.0, 9.5 and 10.0 in a
concealed duplicate design. The robust sweet spot was 9.0--9.5; 8.5 was slightly
constrained and 10 slightly loose. Across the two gates the Owner showed a small
but repeated preference for 9.0 as the more collected setting. Accordingly
tracking is closed at:

```text
LetterSpace = 9
```

This is the robust representative of a near-equivalent visual band, not a claim
that a continuous mathematical optimum is exactly 9.000.

## 4. Phase I.7: punctuation

`build-phase17.sh` compared comma, no punctuation, and interpuncts while keeping
all other selected variables fixed. Each appeared twice in concealed order. The
result was decisive: **no comma and no interpuncts**. The comma disrupted the
visual flow; the interpuncts disrupted the page architecture more strongly.

The selected text is therefore:

```text
CARPE DIEM QVAM MINIMVM CREDVLA POSTERO
```

## 5. Phase I.8--I.11: vertical plaque field

The final page-level issue was not the epigraph face itself but its relation to
the nearby author line. The intended model became explicit: the epigraph plus its
surrounding white space should read as an independent plaque-like page element,
not as a third line belonging ambiguously to the author or abstract.

Phase I.8 and I.9 rejected large downward shifts and the wrong asymmetry direction.
Phase I.10 therefore tested only small upper-side compensation, with the upper
space never larger than the lower. In that blind micro-grid the leading sequence
was approximately:

```text
11/12  >  12/13  ≳  13.5/14
```

with small margins. The important structural result was that `11/12` preserved
the already-comfortable original 12 pt lower gap while increasing the upper gap
from 8 pt to 11 pt and still leaving the upper field 1 pt smaller than the lower.

Phase I.11 was a separate cross-session confirmation using only `8/12`, `11/12`
and `12/13`, each duplicated. All duplicate pairs were correctly recognized. Both
expanded fields (`11/12` and `12/13`) were preferred to the original `8/12`. The
ordering between the two expanded settings reversed by a tiny amount across the
two sessions: Phase I.10 slightly favoured `11/12`; Phase I.11 slightly favoured
`12/13`. This establishes them as one perceptual equivalence band and shows that
further half-point or tenth-point tuning would be overfitting.

The final conservative representative is therefore **11 pt before / 12 pt after**:
it preserves the original lower gap that was already judged comfortable and
changes only the upper interface needed to make the plaque field legible as a
separate element.

## 6. Closed optical specification

The optical experiment is now closed at:

```text
text           CARPE DIEM QVAM MINIMVM CREDVLA POSTERO
family/weight  EB Garamond Medium
LetterSpace    9
size/leading   10.5 / 16
pre-space      11 pt
post-space     12 pt
punctuation    none
kerning        ordinary OpenType kerning
manual fixes   none
```

Do not reopen family, tracking, punctuation or vertical-spacing search without a
new concrete page-level defect. In particular, do not chase sub-point spacing
values inside the observed perceptual-equivalence bands.

## 7. Local build and remote parity

Local builds are the normal iteration path and have been demonstrated to work
without the legacy Trajan chain. Because the Owner's Mac has stale files in
`~/Library/texmf`, the scripts use an empty temporary `TEXMFHOME` by default.

`.github/workflows/epigraph-context.yml` is retained only as a manual
`workflow_dispatch` TeX Live 2025/arXiv-parity utility. It does not block optical
iteration.

Legacy TeX-Live Trajan remains outside the decision gate: repairing its old
Type-1/map/PK fallback chain would add environment noise without improving this
OpenType comparison.

## 8. Publication boundary

No experiment in this directory has changed `paper/manuscript.tex`. The next step,
if authorized, is a separate bounded integration of the closed optical
specification into the publication manuscript, followed by the ordinary
full-manuscript TeX Live/arXiv parity gates.
