#!/bin/sh
set -eu

# Phase I.10: corrected plaque-field micro-grid.
# Fixed: EB Garamond Medium, LetterSpace=9, no punctuation, 10.5/16.
# Vary only vertical white-space field. Upper space is never larger than lower:
# compensation = 0, -0.5pt, or -1pt; lower space = 12, 13, or 14pt.
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
  printf '%s\n' 'E289 Phase I.10: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi
if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.10: missing TeX Live components:' >&2
  printf '  %s\n' "$missing" >&2
  exit 2
fi

rm -f phase20-*.pdf
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

build_one 11   12 phase20-pre11-post12
build_one 11.5 12 phase20-pre11p5-post12
build_one 12   12 phase20-pre12-post12
build_one 12   13 phase20-pre12-post13
build_one 12.5 13 phase20-pre12p5-post13
build_one 13   13 phase20-pre13-post13
build_one 13   14 phase20-pre13-post14
build_one 13.5 14 phase20-pre13p5-post14
build_one 14   14 phase20-pre14-post14

printf '\nBuilt Phase I.10 source proofs.\n'
