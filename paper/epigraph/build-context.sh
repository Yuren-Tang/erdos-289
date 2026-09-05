#!/bin/sh
set -eu

# Build six context proofs.  Run from paper/epigraph or from any directory.
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"

TEXMFHOME=${TEXMFHOME:-/tmp/e289-empty-texmf}
export TEXMFHOME
mkdir -p "$TEXMFHOME"

build_one() {
  variant=$1
  job=$2
  src="\\def\\EpigraphVariant{$variant}\\input{context-specimen.tex}"

  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

build_one 0 context-00-trajan-control
build_one 1 context-01-cinzel-regular
build_one 2 context-02-cinzel-bold
build_one 3 context-03-marcellus-regular
build_one 4 context-04-cormorant-medium
build_one 5 context-05-cormorant-semibold

printf '\nBuilt context proofs:\n'
printf '  %s\n' context-00-trajan-control.pdf \
  context-01-cinzel-regular.pdf \
  context-02-cinzel-bold.pdf \
  context-03-marcellus-regular.pdf \
  context-04-cormorant-medium.pdf \
  context-05-cormorant-semibold.pdf
