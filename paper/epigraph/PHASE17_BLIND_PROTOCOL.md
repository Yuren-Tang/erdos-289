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

The judgement packet was a six-page vector PDF assembled in a concealed randomized order, with each candidate occurring twice. The duplicate pages tested repeatability. The page-to-punctuation key was withheld until after judgement.

## Blind result

The concealed order was:

```text
page 1  comma
page 2  interpunct
page 3  none
page 4  interpunct
page 5  comma
page 6  none
```

The Owner's judgement was decisive: **no interpuncts and no comma**. The comma was judged to break the visual character of the line; the interpunct treatment was judged still worse because the poorly integrated dots disrupted the page architecture itself. Both copies of the punctuation-free setting (pages 3 and 6) therefore agreed with the selected treatment, with no duplicate inconsistency.

Accordingly Phase I.7 closes punctuation at:

```text
CARPE DIEM QVAM MINIMVM CREDVLA POSTERO
```

This gate records a typography decision only. It does not authorize a publication-manuscript change; the selected line is still subject to one final whole-page optical confirmation before integration.
