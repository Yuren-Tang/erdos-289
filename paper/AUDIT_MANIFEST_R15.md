# Erdős Problem 289 — R15 independent-review manifest

**Purpose:** background-blind review of the current manuscript candidate.

**Assurance status before review:** authorial reconstruction only. **No independent PASS is claimed.**

## Review isolation

Before recording an independent verdict, review only the files listed below on the frozen candidate branch. Do **not** inspect `research-workbench`, historical branches, old manuscripts, audit notes, Lean implementation packets, or competing proofs. Those materials may be consulted only after the independent verdict has been recorded.

## Active manuscript source

Read:

- `paper/manuscript.tex`
- `paper/sections/ltar-provider.tex`
- `paper/sections/affine-ray-provider.tex`
- `paper/sections/germ-projections-and-exactification.tex`
- `paper/appendices/source-closed-prefix-certificate.tex`
- `paper/appendices/packing.tex`
- `paper/appendices/prime-supply.tex`
- `paper/appendices/atomic-convolution.tex`
- `paper/references.bib`

No other mathematical source file is an active dependency of this candidate.

## External theorem allowed

The only external combinatorial theorem intentionally used is Haxell's independent-transversal theorem for a graph of maximum degree `Δ` with every partition block of size at least `2Δ`. The bibliography cites the standard 1995 and 2001 sources.

Everything else required for the proof is intended to be proved in the manuscript source above.

## Required blind checks

Please verify, independently and in order:

1. **Source-closed Prefix.** Check the fixed root identities, bridge residue coverage, physical separation, uniform load margin, fixed-complexity homogenization, and especially the uniform moving-window estimate
   \[
   \sup_B N_Q(\operatorname{Prefix}_B)=o(Q/\log Q).
   \]

2. **MasterSlab / defect fibre.** Check the equal-value defect switch, the cardinality pullback, homogeneity, uniform transparency in both `B` and `L`, and the pullback to a fixed defect fibre.

3. **DirectLTAR.** Check signed-inverse downwardness and multiplicity, quota packing and non-reuse of physical atoms, prime convolution coverage, proper-prime-power two-point coverage, targeted filtered lifting, grade finality, resource summability, and the binder order
   \[
   \forall\varepsilon\;\operatorname{Eventually}_B\;\forall O,r\;\operatorname{Eventually}_h.
   \]

4. **Common-source typing.** Check that both affine and Tail responses live over the same endpoint subgroup
   \[
   E_B=H_{\operatorname{lcm}(1,\ldots,B)}
   \]
   and that the source is frozen before defect and final binary count are quantified.

5. **Exactification.** Check the opposite-coset pullback, physical compatibility, the implication
   \[
   [W(f)+W(t)]=0\in\mathbf Q/\mathbf Z,
   \qquad 0<W(f)+W(t)<2
   \Longrightarrow
   W(f\sqcup t)=1,
   \]
   profile addition, and the final quantifier order
   \[
   \exists d_*\;\forall d\ge d_*\;\exists b_0(d)\;\forall b\ge b_0(d).
   \]

Finally check the projection `(b_2,b_3) -> b_2+b_3` proving Erdős Problem 289.

## Verdict format

Record one of:

- `PASS` — no substantive mathematical gap found;
- `PASS WITH EDITORIAL FIXES` — proof closed, only non-mathematical corrections required;
- `FAIL` — give the first minimal substantive gap and the exact dependency it breaks;
- `INCOMPLETE` — specify exactly which step could not be verified.

Do not infer assurance from repository history, previous audit language, formalization progress, or author statements.
