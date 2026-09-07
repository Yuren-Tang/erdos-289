# Reciprocal Sums over Separated Integer Intervals

**Yuren Tang**  
ORCID: [0009-0006-0847-3330](https://orcid.org/0009-0006-0847-3330)

This repository contains the manuscript, source, and finite-certificate checker for *Reciprocal Sums over Separated Integer Intervals*.

The paper proves that, for every sufficiently large integer \(k\), there is a finite set of positive integers whose path-graph connected components are exactly \(k\) pairwise nonadjacent intervals, each of cardinality 2 or 3, and whose reciprocal sum is 1. In particular, it gives an affirmative answer to the strengthened disjoint, nonadjacent formulation currently listed as Erdős Problem 289.

## Manuscript

- [Reciprocal Sums over Separated Integer Intervals.pdf](<Reciprocal Sums over Separated Integer Intervals.pdf>) — compiled manuscript
- `main.tex` — root TeX source
- `sections/` — main sections
- `appendices/` — appendices
- `references.bib` — bibliography

## Build

The manuscript uses XeLaTeX and BibLaTeX/Biber. A current complete TeX Live or MacTeX installation is recommended.

```sh
sh build.sh
```

Equivalently:

```sh
xelatex main.tex
biber main
xelatex main.tex
xelatex main.tex
```

The source uses standard TeX Live packages and loads ET Bembo and EB Garamond by OpenType filename from TeX Live.

## Finite certificate

Appendix C contains an exact finite initialization certificate. Its rational and polynomial checks can be reproduced with Python 3 using only the standard library:

```sh
python3 verification/check_finite_certificate.py
```

The checker verifies only the finite certificate and the reciprocal-neutral polynomial identity. It does **not** verify the infinite argument, asymptotic estimates, external theorems, or the paper as a whole.

## Repository scope

Only publication-facing manuscript material is kept on the main line of this repository. Historical drafts, review notes, audit ledgers, and private working artifacts are intentionally excluded.

No repository-wide license has yet been selected. Copyright therefore remains with the author except where otherwise stated.
