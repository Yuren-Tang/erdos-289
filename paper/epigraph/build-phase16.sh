#!/bin/sh
set -eu

# Phase I.6: fine tracking bracket for the surviving EB Garamond Medium cut.
# Only tracking varies. Wording, comma, 10.5/16 and 8pt/12pt title-matter
# spacing remain fixed.
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
  printf '%s\n' 'E289 Phase I.6: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi

if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.6: missing TeX Live components:'
  printf '  %s\n\n' "$missing"
  printf '%s\n' 'Install them once with:'
  printf '  sudo tlmgr update --self\n'
  printf '  sudo tlmgr install%s\n' "$missing"
  exit 2
fi

rm -f phase16-*.pdf

build_one() {
  tracking=$1
  job=$2
  src="\\def\\EpigraphVariant{0}\\def\\EpigraphTracking{$tracking}\\input{context-specimen.tex}"

  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

# Fine bracket around the Phase-I.5 optimum. The blind collation itself is
# intentionally not encoded in this repository script: exposing the order here
# would defeat the test. The four canonical source proofs remain reproducible.
build_one 8.5  phase16-medium-ls085
build_one 9.0  phase16-medium-ls090
build_one 9.5  phase16-medium-ls095
build_one 10.0 phase16-medium-ls100

printf '\nBuilt Phase I.6 source proofs:\n'
printf '  %s\n' \
  phase16-medium-ls085.pdf \
  phase16-medium-ls090.pdf \
  phase16-medium-ls095.pdf \
  phase16-medium-ls100.pdf
