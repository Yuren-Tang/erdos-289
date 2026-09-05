# Phase I.12 / Phase 22: no-background integrated blind review

Purpose: obtain one final independent judgement of the integrated first page **without exposing the typography search history or identifying the epigraph as the element under test**.

## Source object

The review source is the first page of the full publication manuscript produced by the fixed TeX Live 2025-08-03 workflow after bounded integration of the closed optical specification.

Integration source commit:

```text
d17303db92c1887495459856fb75873bcb0100e1
```

Authoritative parity run:

```text
GitHub Actions run 33989122234
conclusion: success
artifact: e289-publication-manuscript
artifact id: 9976093392
artifact digest: sha256:e03c5fd2b7a11fd6cf209dd1c7a6323fc54309beae75996162c0586ae2767ae2
pages: 27 A4
```

The one-page review copy is extracted directly from page 1 of that artifact. Its PDF metadata is cleared; its page content and embedded vector fonts are unchanged.

## Blindness rule

The reviewer must not receive any of the following before giving the judgement:

- the E306 reference or its typography;
- the former Trajan treatment;
- any family/weight candidate list;
- tracking values or tracking-blind-test results;
- punctuation alternatives or results;
- vertical-spacing values or results;
- any statement that the epigraph is the focus of the review;
- any previous Owner or assistant assessment.

The reviewer receives only the finished first-page PDF and the neutral review prompt below.

## Neutral reviewer prompt

> You are reviewing the first page of a mathematical manuscript with no information about its design history.
>
> Treat the page as a finished, unknown design. Do not assume that any particular line, font, spacing choice, or element is the subject of the test. Do not compare it with an imagined earlier version. Judge only what is visible in the supplied PDF.
>
> Please review the page as a whole, with special attention to:
>
> 1. the first-impression visual hierarchy and whether the page reads coherently from title through the beginning of the article;
> 2. whether any element feels stylistically foreign, over- or under-emphasized, accidentally grouped with a neighbour, or insufficiently integrated into the page architecture;
> 3. whether any visible spacing, weight, letterspacing, punctuation, alignment, or vertical-rhythm choice creates tension or ambiguity;
> 4. whether the page feels like one composed system rather than several separately designed pieces;
> 5. whether you would accept the page unchanged. If not, identify the smallest specific change you would make and explain the visual reason.
>
> Do not invent a defect merely to be helpful. If the page is already coherent and further tuning would likely be overfitting, say so explicitly.
>
> Give your initial impression first, before detailed analysis.

## Decision rule

The blind review is diagnostic, not another optimization search.

- If the reviewer accepts the page unchanged or identifies no concrete integrated defect, close typography permanently.
- If the reviewer independently identifies a clear defect, first check whether it is reproducible and page-level rather than a personal micro-preference.
- Do **not** reopen broad family/tracking/spacing searches in response to vague language such as “perhaps slightly different”. Any reopening requires a specific defect with a specific local mechanism.
- The blind reviewer is not told which historical parameter values are available; therefore any genuinely convergent criticism is evidence independent of the earlier search.

## Separation from the experiment history

The blind-review PDF and prompt may be passed to a fresh chat/model or a human reviewer. The current research conversation is not a valid blind-review environment because it contains the full optimization history. The review response should be frozen before this protocol or the experiment history is shown to that reviewer.
