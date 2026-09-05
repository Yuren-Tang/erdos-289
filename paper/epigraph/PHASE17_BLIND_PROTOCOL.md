# Phase I.7 blind punctuation protocol

Purpose: choose the punctuation treatment only after family/weight and tracking have been provisionally closed.

## Fixed parameters

- family/weight: EB Garamond Medium;
- tracking: `LetterSpace=9`;
- wording: Horace line in all caps with `V` for `U`;
- size/leading: 10.5/16;
- title-matter spacing: 8 pt before, 12 pt after;
- ordinary OpenType kerning; no hand kerning or synthetic emboldening.

## Candidate source proofs

`build-phase17.sh` reproducibly builds three complete first-page candidates:

1. comma: `CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO`;
2. no punctuation: `CARPE DIEM QVAM MINIMVM CREDVLA POSTERO`;
3. interpuncts: `CARPE · DIEM · QVAM · MINIMVM · CREDVLA · POSTERO`.

The judgement packet is a six-page vector PDF assembled in a concealed randomized order, with each candidate occurring twice. The duplicate pages test repeatability. The page-to-punctuation key must not be committed or disclosed until the Owner has ranked the pages.

The Owner should inspect at fixed zoom and report best/worst pages, approximate tiers, and any pages that appear identical. Because punctuation differences are larger than the Phase I.6 tracking differences, failure to identify duplicate copies would be evidence that page-order/attention noise is unusually strong and should count against over-interpreting small preferences.

This gate decides visual/editorial punctuation only. It does not authorize a publication-manuscript change; the surviving punctuation treatment is still subject to the final page-context check before integration.
