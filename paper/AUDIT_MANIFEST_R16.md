# Erdős Problem 289 — R16 background-blind review manifest

## Scope

This branch is a mathematical review candidate. Please assess the proof from the active manuscript sources alone.

Before recording a verdict, **do not read**:

- `paper/README.md`;
- any earlier candidate branch or audit manifest;
- repository commit history or diffs;
- `Yuren-Tang/research-workbench`;
- Lean/formalisation packets;
- any previous review or discussion of this proof;
- any competing proof of Erdős Problem 289.

The authorised mathematical sources are exactly:

1. `paper/manuscript.tex`;
2. `paper/sections/ltar-provider.tex`;
3. `paper/sections/affine-ray-provider.tex`;
4. `paper/sections/germ-projections-and-exactification.tex`;
5. `paper/appendices/source-closed-prefix-certificate.tex`;
6. `paper/appendices/packing.tex`;
7. `paper/appendices/prime-supply.tex`;
8. `paper/appendices/atomic-convolution.tex`;
9. `paper/references.bib`.

No statement outside these files is intended to fill a mathematical gap.

## Requested reconstruction

Please reconstruct the proof from the theorem statement to Erdős Problem 289 and record a verdict before consulting any excluded material.

In particular, verify the following interfaces literally rather than by intended meaning.

### A. Source and endpoint quantifiers

Check that

- the source index is the ordinary tail `B -> infinity` on `N`;
- `E_B = H_{lcm(1,...,B)}` is cofinal among finite subgroups of `Q/Z`;
- the boundary-predecessor definition and escape estimate are sufficient for every below-source predecessor occurrence used by the Tail;
- the small-resource tolerance is quantified before the source threshold;
- the final source is frozen before defect and final binary count.

### B. Literal affine-coset coverage

Check that

- the fixed root and scale-proper bridges give one full literal affine coset at `E_B`;
- grade homogenisation translates that coset by one common exact value;
- the defect selector changes profile but not residue;
- the resulting MasterSlab map
  `(res,b_3): S_{B,L} -> q_{E_B}^{-1}(a_{B,L}) x [d_0(B),L]`
  is genuinely surjective;
- the fixed-defect affine ray is a pullback of this map, with one constant component profile.

### C. Moving-window transparency

Check that

- retained Tail centres are globally injective and lie in the stated current window;
- complete-envelope incidence controls the number of killed Tail atoms;
- the Prefix `sup_B N_Q = o(Q/log Q)` estimate implies a uniform positive survivor fraction;
- the same statement covers boundary predecessors;
- after adding the quadratically separated defect cube, the estimate is uniform in both `B` and the slab ceiling `L`.

### D. One packing and local covers

Check that

- Haxell's theorem is used with its correct hypotheses;
- one global independent packing is formed before local simple-cover constructions;
- own-cover and successor-donor roles are allocated disjointly whenever they can occur simultaneously;
- the prime-current convolution theorem gives every grade in its claimed interval;
- the square and higher-prime-power two-point constructions really cover the prime-order simple factor;
- targeted filtered lifting handles lower shadows without a splitting or representative choice;
- grade intervals become final and all reciprocal-mass majorants are summable.

### E. Exactification

At the single frozen source, verify that the opposite-coset pullback is surjective over the Tail family, that physical compatibility survives the matching, and that

`[W(f)+W(t)] = 0 in Q/Z` together with `0 < W(f)+W(t) < 2`

forces exact value `1`. Finally check the component-profile and quantifier projection to Erdős Problem 289.

## External theorem

The manuscript intends to use only the cited Haxell independent-transversal theorem as an external combinatorial theorem. Please flag any other step that in fact needs a nontrivial external theorem or an unstated hypothesis.

## Verdict

Please use one of:

- `PASS`;
- `PASS WITH EDITORIAL FIXES`;
- `INCOMPLETE`;
- `FAIL`.

For every non-PASS verdict, distinguish a mathematical gap from an exposition/definition omission and identify the earliest point at which reconstruction fails.

This manifest is a review protocol only. It makes no claim that the manuscript has already passed an independent review or a completed formal verification.
