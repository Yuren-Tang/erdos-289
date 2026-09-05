#!/bin/sh
set -eu

# Phase I.8: vertical plaque-spacing gate for the selected epigraph.
# Family/weight, tracking, wording, punctuation, size/leading and total added
# title-matter space are fixed. Only the allocation of the same 20pt total
# space above and below the epigraph varies.
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
  printf '%s\n' 'E289 Phase I.8: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi

if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.8: missing TeX Live components:'
  printf '  %s\n\n' "$missing"
  printf '%s\n' 'Install them once with:'
  printf '  sudo tlmgr update --self\n'
  printf '  sudo tlmgr install%s\n' "$missing"
  exit 2
fi

rm -f phase18-*.pdf

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

# All candidates preserve pre + post = 20pt, so the abstract and the rest of
# the page remain at the same vertical coordinate. Only the epigraph moves
# within a fixed-height title-matter slot.
build_one 8  12 phase18-pre08-post12
build_one 10 10 phase18-pre10-post10
build_one 11  9 phase18-pre11-post09
build_one 12  8 phase18-pre12-post08
build_one 14  6 phase18-pre14-post06

printf '\nBuilt Phase I.8 source proofs:\n'
printf '  %s\n' \
  phase18-pre08-post12.pdf \
  phase18-pre10-post10.pdf \
  phase18-pre11-post09.pdf \
  phase18-pre12-post08.pdf \
  phase18-pre14-post06.pdf
