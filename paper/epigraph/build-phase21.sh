#!/bin/sh
set -eu

# Phase I.11: cross-session confirmation gate.
# Fixed: EB Garamond Medium, LetterSpace=9, no punctuation, 10.5/16.
# Compare only three previously motivated vertical settings:
#   8/12  = original E306-derived geometry;
#   11/12 = Phase I.10 provisional leader;
#   12/13 = adjacent larger-field alternative.
# The blind six-page packet duplicates each source proof, but its concealed
# randomized order is intentionally not encoded in this repository script.
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"

TEXMFHOME=${TEXMFHOME:-/tmp/e289-empty-texmf}
export TEXMFHOME
mkdir -p "$TEXMFHOME"

missing=""
need_tex() {
  file=$1
  pkg=$2
  if ! kpsewhich "$file" >/dev/null 2>&1; then
    missing="$missing $pkg"
  fi
}
need_tex newtxmath.sty newtx
need_tex ETbb-Regular.otf etbb
need_tex EBGaramond-Medium.otf ebgaramond
need_tex EBGaramond-Regular.otf ebgaramond
need_tex microtype.sty microtype
need_tex enumitem.sty enumitem
need_tex csquotes.sty csquotes
need_tex biblatex.sty biblatex
need_tex hyperref.sty hyperref
need_tex cinzel.sty cinzel
need_tex marcellus.sty marcellus
need_tex CormorantGaramond.sty cormorantgaramond
if ! command -v xelatex >/dev/null 2>&1; then
  printf '%s\n' 'E289 Phase I.11: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi
if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.11: missing TeX Live components:' >&2
  printf '  %s\n' "$missing" >&2
  exit 2
fi

rm -f phase21-*.pdf
build_one() {
  pre=$1
  post=$2
  job=$3
  src="\\def\\EpigraphVariant{0}\\def\\EpigraphTracking{9}\\def\\EpigraphText{CARPE DIEM QVAM MINIMVM CREDVLA POSTERO}\\def\\EpigraphPreSpace{${pre}pt}\\def\\EpigraphPostSpace{${post}pt}\\input{context-specimen.tex}"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

build_one 8  12 phase21-pre08-post12
build_one 11 12 phase21-pre11-post12
build_one 12 13 phase21-pre12-post13

printf '\nBuilt Phase I.11 canonical source proofs.\n'
