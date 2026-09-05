# Phase I.9 blind plaque-field size protocol

Purpose: implement the Owner's preferred visual model of the epigraph as an independent plaque-like page element, with roughly equal visible white space above and below, while varying the overall size of that white-space field.

## Fixed parameters

- family/weight: EB Garamond Medium;
- tracking: `LetterSpace=9`;
- wording: `CARPE DIEM QVAM MINIMVM CREDVLA POSTERO`;
- punctuation: none;
- size/leading: 10.5/16;
- ordinary OpenType kerning; no hand kerning or synthetic emboldening.

## Optical-centering relation

Phase I.8 showed that holding the old 20pt total space fixed made the title matter too compressed. Its useful geometric result was instead the optical offset: the visible plaque field is approximately centred when

```text
pre-space = post-space + 2 pt.
```

Phase I.9 therefore preserves that relation and varies only the absolute size of the field.

The five source proofs are:

- 12/10 pt;
- 13/11 pt;
- 14/12 pt;
- 15/13 pt;
- 16/14 pt.

The 14/12 proof is the conceptual anchor. It keeps the original E306-derived 12pt epigraph-to-abstract spacing, which the Owner judged comfortable, and enlarges only the upper field enough to match it optically.

## Blind packet

The judgement packet contains six unlabeled first pages drawn from the five source proofs, with the 14/12 anchor duplicated to test repeatability. Page order and the page-to-parameter key are kept out of repository history until judgement is complete.

Judge whether the epigraph plus surrounding white space reads as a self-contained plaque inserted between the author block and abstract, and whether the plaque field itself feels too tight, too loose, or balanced.

No publication-manuscript change is authorized by this experiment.
