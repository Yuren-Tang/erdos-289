# Phase I.11 cross-session confirmation protocol

Purpose: perform one final confirmatory blind test of the vertical-spacing decision without opening any new tuning axis.

## Fixed parameters

- family/weight: EB Garamond Medium;
- tracking: `LetterSpace=9`;
- wording: `CARPE DIEM QVAM MINIMVM CREDVLA POSTERO`;
- punctuation: none;
- size/leading: 10.5/16;
- ordinary OpenType kerning; no hand kerning or synthetic emboldening.

## Confirmatory candidates

Only three previously motivated vertical settings are retained:

1. `8/12` pt — original E306-derived baseline;
2. `11/12` pt — Phase I.10 provisional leader;
3. `12/13` pt — adjacent larger-field alternative that also ranked near the top.

`build-phase21.sh` reproduces these three canonical full first-page proofs.

## Blind packet

The judgement packet contains six unlabeled vector pages in concealed randomized order, with each of the three candidates appearing exactly twice. The page-to-parameter key was kept out of repository history until the Owner had reported the judgement.

This is intentionally a **cross-session confirmation**, not another search for a finer optimum. The useful questions are:

- do the two copies of a given setting receive broadly consistent impressions;
- does `11/12` remain in the top tier after visual memory of the Phase I.10 grid has faded;
- is the original `8/12` still visibly too close to the author once judged against the two expanded plaque fields;
- does `12/13` improve separation enough to justify the extra total title-matter height.

## Decision rule

- If `11/12` again ranks clearly or consistently in the top tier, close vertical spacing at `11/12` and stop tuning.
- If `8/12`, `11/12`, and `12/13` collapse into one perceptual tier or duplicate judgements are materially inconsistent, treat the residual difference as below reliable visual resolution. Do not introduce half-point or tenth-point refinements. Prefer the simplest design justified by the accumulated evidence rather than overfitting the final session.
- This gate does not authorize a publication-manuscript change. Integration remains a separate bounded step after the optical choice is closed.

## Revealed key

The Owner first reported that pages 5/6, 2/3, and 1/4 were respectively identical pairs, and judged pages 4 and 5 very difficult to distinguish but both better than page 3, with a very small final inclination toward page 5.

The concealed key was:

```text
pages 2,3 = 8/12
pages 1,4 = 11/12
pages 5,6 = 12/13
```

Thus all three duplicate pairs were recognized correctly. Both expanded plaque fields (`11/12` and `12/13`) were preferred to the original `8/12` baseline. The only unstable distinction was between the two expanded settings themselves: Phase I.10 had given `11/12` a slight edge over `12/13`, whereas this confirmation gave `12/13` a slight edge over `11/12`.

## Conclusion

The robust result is therefore not a sub-point optimum but a **perceptual equivalence band consisting of the two expanded plaque fields**. The original `8/12` geometry is rejected for E289 because its upper gap is too tight relative to the intended independent-plaque reading. The residual `11/12` versus `12/13` ordering is below reliable visual resolution and must not be used to justify further micro-tuning.

For the final design choice, use `11/12` as the conservative representative of this equivalence band: it preserves the already-comfortable original 12 pt lower gap and changes only the upper gap, while maintaining the intended slight upper-side optical compensation. `12/13` remains visually equivalent evidence, not a reason to open another spacing search.

Vertical spacing is now **closed**. No further point, half-point, or tenth-point search is authorized by this experiment.

No publication-manuscript change has yet been made.
