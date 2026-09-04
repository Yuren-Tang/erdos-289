# Paper workbench — categorical exactification

This branch is the public editorial workbench for the manuscript on Erdős Problem 289.

## Authority boundary

Mathematical developments are maintained on the mathematical research side and enter this branch only after their proof role has been identified. This branch is for the manuscript, commuting diagrams, bibliography, provenance, and publication-facing audits.

Intermediate commits are work in progress. They are **not** claimed to be independently verified final statements. The Lean formalization is ongoing and is **not** claimed to constitute a complete formal proof of Erdős Problem 289.

## Independent-review status

The frozen branch `paper/candidate-r15` received a genuinely independent background-blind review with verdict **INCOMPLETE — Major Revision**. The review did not find evidence that the main theorem is false and accepted many concrete components, but correctly identified missing proof interfaces in the manuscript. In particular, R15 did not adequately define its source filter, did not make the affine-coset coverage interface literal, and left the window-to-transparency and disjoint-allocation bridges implicit.

R16 is the working repair. It does **not** inherit an independent PASS from the R15 review. A fresh independent review is required after R16 is frozen.

## Current active proof spine

The manuscript proves the stronger fibrewise component-profile statement and then projects to Erdős Problem 289. Its active dependency graph is:

1. regular-image / pullback bookkeeping and the target quotient `Q/Z`;
2. the intrinsic component profile `(b_2,b_3)`;
3. the ordinary source filter `B -> infinity`, endpoint groups `E_B = H_{lcm(1,...,B)}`, and the explicit boundary-predecessor escape lemma;
4. a **source-closed** affine ray built from
   - one fixed finite affine root certificate,
   - scale-proper simple compact bridges,
   - literal affine-coset accumulation,
   - fixed-complexity grade homogenization,
   - a uniform moving-source transparency estimate,
   - equal-value defect translation and a cardinality pullback;
5. a direct late-source targeted Tail response built from
   - signed-inverse transverse binary rows,
   - globally injective distinguished centres and bounded conflict degree,
   - complete-envelope sparse survival,
   - one global Haxell packing followed by disjoint own/donor allocations,
   - finite convolution-support covers at prime simple factors,
   - elementary two-point covers at proper prime powers,
   - target-specific filtered lifting,
   - grade finality and summable reciprocal-mass decay;
6. freezing one common endpoint source after the two ordinary source thresholds;
7. same-source opposite-coset pullback and literalization in `(0,2)`, giving exact reciprocal value `1`;
8. projection from the joint component-profile spectrum to total component count.

The small-resource tolerance is quantified before the source threshold. The common endpoint source is then frozen before the defect and final binary count are quantified. Fixed-source arbitrarily-small positive saturation is false.

## R16 repairs relative to candidate-r15

R16 deliberately does not implement the independent review's repair suggestions verbatim when a stronger historical abstraction is already available.

- The old `eligible-base` language is deleted rather than formalized. The source object is `N` with `atTop`; boundary predecessors are a derived finite boundary object whose ranks escape uniformly.
- The undefined `Required(phi)` interface is deleted rather than restored. Prefix and MasterSlab now prove literal regular epimorphisms onto affine cosets `q_{E_B}^{-1}(a)`.
- The Prefix estimate `sup_B N_Q = o(Q/log Q)` is connected to Tail survival by an explicit complete-envelope sparse-survival lemma, uniform over obstacle collections.
- The Tail now proves distinguished-centre injectivity and bounded conflicts, then performs one global independent packing and explicit disjoint own/donor allocations inside it.
- The atomic-convolution appendix explicitly handles odd cardinality and states absolute threshold constants.

## What is certificate data, not ontology

The source-closed Prefix proof still needs a **fixed finite root certificate**. Its explicit `H_6` reciprocal identities and the finitely many early bridge checks live only in the appendix and have no consumer above the Prefix theorem. In particular, no exact large rational total or distinguished finite margin is part of the theorem interface.

The current manuscript does **not** use the following as active dependencies:

- generic remote finite mobility as the moving-source Prefix provider;
- Dias da Silva–Hamidoune / restricted-fold saturation;
- the historical full BinaryTail correction cover;
- a least absorber in the final exactification;
- D-supercritical grade aggregation;
- a common Tail across different defect fibres;
- an independent ordinary exact-grade root;
- the full generic correction-composition engine as a manuscript prerequisite.

These remain available in Git history or the research workbench as historical/alternative mathematics where applicable.

## Proof-assurance status

R16 is an authorial repair in response to an independent `INCOMPLETE` review. The repaired interfaces have been checked against the historical source-closed Prefix and one-packing constructions, but **no independent mathematical PASS is claimed for R16**. The next assurance step is a fresh background-blind review of a frozen R16 candidate.
