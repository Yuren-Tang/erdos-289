# Phase I.6 blind tracking protocol

Purpose: resolve the remaining EB Garamond Medium tracking choice without allowing parameter labels or presentation order to bias the optical judgement.

## Fixed parameters

- family/weight: EB Garamond Medium;
- wording: `CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO`;
- punctuation: comma retained;
- size/leading: 10.5/16;
- title-matter spacing: 8 pt before, 12 pt after;
- ordinary OpenType kerning; no hand kerning or synthetic emboldening.

## Candidate source proofs

`build-phase16.sh` reproducibly builds four complete first-page candidates at `LetterSpace=8.5`, `9.0`, `9.5`, and `10.0`.

The actual judgement packet is a six-page vector PDF assembled in a concealed randomized order. The 9.0 and 9.5 candidates each occur twice. The duplicate pages test within-session repeatability; their positions and the page-to-parameter key must not be recorded in the repository until the Owner has ranked the pages.

The Owner should inspect the six pages at a fixed zoom and report, preferably before prolonged pairwise comparison:

1. best page(s);
2. worst page(s);
3. an approximate ordering or tiers if discernible;
4. any pages that appear indistinguishable.

Only after that report is frozen should the page-to-parameter key be revealed. If duplicate copies receive materially inconsistent judgements, treat differences in the 9--9.5 region as below reliable visual resolution and prefer the simpler/frozen-nearest setting rather than overfitting.

No publication manuscript change is authorized by this experiment.
