# Reciprocal Sums over Separated Integer Intervals

**Yuren Tang**  
ORCID: [0009-0006-0847-3330](https://orcid.org/0009-0006-0847-3330)

This repository contains the manuscript, source, and finite-certificate checker for *Reciprocal Sums over Separated Integer Intervals*.

The paper proves that, for every sufficiently large integer $k$, there is a finite set of positive integers whose path-graph connected components are exactly $k$ pairwise nonadjacent intervals, each of cardinality 2 or 3, and whose reciprocal sum is 1. In particular, it gives an affirmative answer to the strengthened disjoint, nonadjacent formulation of [Erdős Problem 289](https://www.erdosproblems.com/289).

## Manuscript

- [Reciprocal Sums over Separated Integer Intervals.pdf](<Reciprocal Sums over Separated Integer Intervals.pdf>) — compiled manuscript
- `main.tex` — root TeX source
- `sections/` — main sections
- `appendices/` — appendices
- `references.bib` — bibliography

## Build

The manuscript is built with XeLaTeX and BibLaTeX/Biber via `latexmk`. Its TeX packages and OpenType fonts are standard TeX Live components; the GitHub Actions workflow records a tested package set.

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

## Verification

Appendix C contains an exact finite initialization certificate. Its rational and polynomial checks can be reproduced with Python 3 using only the standard library:

```sh
python3 verification/check_finite_certificate.py
```

The checker verifies only the finite certificate and the reciprocal-neutral polynomial identity. It does **not** verify the infinite argument, asymptotic estimates, external theorems, or the paper as a whole.

The GitHub Actions workflow `.github/workflows/manuscript.yml` performs, from a clean checkout:

1. the finite-certificate check;
2. a complete XeLaTeX/Biber build via `build.sh`;
3. a check that the publication-facing PDF is produced and has 40 pages.

A green workflow therefore certifies the release build pipeline and the finite certificate, not the correctness of the mathematical proof as a whole.

## License

No repository-wide license has yet been selected. Copyright therefore remains with the author except where otherwise stated.
