# Reciprocal Sums over Separated Integer Intervals

**Yuren Tang**  
ORCID: [0009-0006-0847-3330](https://orcid.org/0009-0006-0847-3330)

This repository contains the manuscript, source, and exact-arithmetic verifier for *Reciprocal Sums over Separated Integer Intervals*.

The paper proves that, for every sufficiently large integer $k$, there is a finite set of positive integers whose path-graph connected components are exactly $k$ pairwise nonadjacent intervals, each of cardinality 2 or 3, and whose reciprocal sum is 1. In particular, it gives an affirmative answer to the strengthened disjoint, nonadjacent formulation of [Erdős Problem 289](https://www.erdosproblems.com/289).

## Manuscript

- [Reciprocal Sums over Separated Integer Intervals.pdf](<Reciprocal Sums over Separated Integer Intervals.pdf>) — compiled manuscript
- `main.tex` — root TeX source
- `sections/` — main sections
- `appendices/` — appendices
- `references.bib` — bibliography

## Build

The manuscript is built with XeLaTeX and BibLaTeX/Biber via `latexmk`. Its TeX packages and OpenType fonts are standard TeX Live components; the manuscript workflow records a tested package set.

On POSIX systems, the complete publication build can be run with

```sh
sh build.sh
```

`build.sh` invokes `latexmk` and then writes the publication-facing artifact to

```text
Reciprocal Sums over Separated Integer Intervals.pdf
```

The intermediate `main.pdf` is ignored by Git. On other platforms, the TeX build may be invoked directly with

```text
latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
```

which produces `main.pdf`. `build.sh` additionally copies that output to the title-named publication-facing artifact tracked in the repository.

The GitHub Actions workflow `.github/workflows/manuscript.yml` performs the same build from a clean checkout and checks the title, author, and 40-page layout of the resulting publication artifact.

## Exact arithmetic

Appendix C gives an explicit finite initialization, and Equation (3.1) gives the reciprocal-neutral identity used in the construction. Their exact rational and polynomial arithmetic can be recomputed with Python 3 using only the standard library:

```sh
python3 verification/verify_exact_arithmetic.py
```

The verifier checks the five seed identities and common-denominator certificates, the displayed finite separation data and exceptional bridge arithmetic, the rational mass bounds, and the polynomial identity (3.1). All of these calculations are stated in the manuscript; the script provides an independently executable recomputation for reader convenience.

The GitHub Actions workflow `.github/workflows/exact-arithmetic.yml` runs this verifier independently from the manuscript build.

## License

No repository-wide license has yet been selected. Copyright therefore remains with the author except where otherwise stated.
