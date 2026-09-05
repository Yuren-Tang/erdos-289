# Phase I.8 blind vertical plaque-spacing protocol

Purpose: test whether the selected epigraph reads more cleanly as an independent page element when it is optically centred inside its own surrounding white-space field.

## Fixed parameters

- family/weight: EB Garamond Medium;
- tracking: `LetterSpace=9`;
- wording: `CARPE DIEM QVAM MINIMVM CREDVLA POSTERO`;
- punctuation: none;
- size/leading: 10.5/16;
- ordinary OpenType kerning; no hand kerning or synthetic emboldening.

The experiment does **not** change the total added vertical title-matter space. Every source proof keeps

```text
pre-space + post-space = 20 pt.
```

Therefore the title, author, abstract and the rest of the page remain vertically fixed; only the epigraph moves inside a fixed-height slot. This isolates the intended visual model: the epigraph plus its surrounding blank field behaves like one inserted plaque rather than a third text line belonging ambiguously to the author or abstract.

## Source proofs

`build-phase18.sh` builds:

- 8/12 pt: the current E306-derived baseline;
- 10/10 pt;
- 11/9 pt;
- 12/8 pt;
- 14/6 pt as a deliberately lower-shifted boundary specimen.

A local bounding-box audit of the actual first-page glyphs found that the baseline leaves the visible author-to-epigraph gap smaller than the epigraph-to-abstract gap. With the page flow held fixed, 11/9 places the visible gaps within about 0.2 pt of one another in the local TeX Live build. This measurement is only a geometric reference; optical judgement remains authoritative.

## Blind packet

The judgement packet uses six unlabeled vector pages. It contains the current 8/12 baseline, 10/10, 11/9, and 12/8, with the two near-centre candidates duplicated to test repeatability. The page-to-parameter key is kept out of repository history until judgement is complete.

Judge the whole title block at a fixed zoom. In particular, ask whether the epigraph and its surrounding white space read as one centred page element, and whether the author is thereby more clearly grouped with the title rather than with the epigraph.

No publication-manuscript change is authorized by this experiment.
