#!/bin/sh
set -eu

# Phase I.7: punctuation gate for the selected EB Garamond Medium / LS9 line.
# Only punctuation treatment varies. Family/weight, tracking, wording, 10.5/16
# and 8pt/12pt title-matter spacing remain fixed.
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
  printf '%s\n' 'E289 Phase I.7: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi

if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.7: missing TeX Live components:'
  printf '  %s\n\n' "$missing"
  printf '%s\n' 'Install them once with:'
  printf '  sudo tlmgr update --self\n'
  printf '  sudo tlmgr install%s\n' "$missing"
  exit 2
fi

rm -f phase17-*.pdf

build_one() {
  text=$1
  job=$2
  src="\\def\\EpigraphVariant{0}\\def\\EpigraphTracking{9}\\def\\EpigraphText{$text}\\input{context-specimen.tex}"

  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

# Three canonical source proofs. The blind packet is collated separately so its
# randomized duplicate order is not disclosed by repository history.
build_one 'CARPE DIEM, QVAM MINIMVM CREDVLA POSTERO' \
  phase17-comma
build_one 'CARPE DIEM QVAM MINIMVM CREDVLA POSTERO' \
  phase17-none
build_one 'CARPE · DIEM · QVAM · MINIMVM · CREDVLA · POSTERO' \
  phase17-interpunct

printf '\nBuilt Phase I.7 source proofs:\n'
printf '  %s\n' \
  phase17-comma.pdf \
  phase17-none.pdf \
  phase17-interpunct.pdf
