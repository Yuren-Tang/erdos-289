# Global integrated blind-review protocol

Purpose: obtain a publication-level, no-background review of the **entire mathematical manuscript** after epigraph integration. This is explicitly not another first-page typography review.

## Review object

The authoritative review object is the 27-page manuscript PDF produced by the fixed TeX Live 2025-08-03 publication workflow after bounded integration of the closed epigraph specification.

- publication-source integration commit: `d17303db92c1887495459856fb75873bcb0100e1`
- authoritative parity run: GitHub Actions `33989122234`
- conclusion: `success`
- artifact: `e289-publication-manuscript`
- artifact id: `9976093392`
- local extracted PDF sha256: `febebf78cf6c9900e055c91c26b3c69a9557d50fa3969f1792c7427cbaed6d08`
- pages: 27 A4

## Blindness boundary

Before the reviewer freezes a report, do not provide:

- repository history or earlier proof architectures;
- Lean/formalization status;
- previous mathematical audits or assistant/user discussion;
- typography experiments or their rationale;
- known suspected weak points, if any;
- claims about how close the manuscript is to publication readiness.

The reviewer may use standard mathematical knowledge and may verify cited external theorems when genuinely needed, but must separate such external verification from the manuscript-internal audit and must not search the author's repository or discussion history.

## Scope

The review is global and adversarial. The reviewer must first reconstruct the theorem and proof dependency graph, then try to break every load-bearing interface. Required coverage includes:

- labelled-relation / partial-monoid calculus and strictification under joint compatibility;
- the Q/Z torsion filtration and prime-power simple quotients;
- neutral switches, comparable-prime supply, and the signed-inverse families;
- finite initialization and the wide affine initial cover;
- fixed-cardinality sum surjectivity and the large-image / heavy-fibre transfer;
- uniform demand and prime gain;
- scalar continuation, accumulated composite debt, and affine-centre vanishing;
- Haxell thinning only after a finite cutoff;
- affine lifting, joint compatibility, exact finite composition, and reciprocal-mass control;
- terminal pullback and the final inference `W=1`;
- appendices versus the exact promises consumed in the main text;
- quantifier order, constant dependence, finite/infinite interchanges, and hidden circularity.

The reviewer must independently re-derive at least three load-bearing quantitative or categorical steps rather than only paraphrasing them.

## Severity classes

Every finding must be classified as one of:

- `BLOCKER`
- `MAJOR`
- `MINOR`
- `EDITORIAL`

Every non-editorial finding must give an exact location, the precise claim, the failure mechanism, whether the main theorem is endangered, and the smallest plausible repair if visible.

## Decision rule

The review is diagnostic, not an invitation to invent changes.

- If no concrete mathematical defect is found, record that explicitly.
- Vague delicacy or stylistic discomfort is not a mathematical finding.
- A real gap is not downgraded merely because a repair looks plausible.
- If a specific issue is found, freeze the report before exposing the reviewer to project history, then analyze the issue against the actual dependency graph.

The full neutral reviewer prompt is distributed outside the repository together with the authoritative manuscript PDF so that the review can be performed in a fresh chat/model or by a human referee.
