#!/bin/sh
set -eu

# Phase I.5: isolate the source of the E306-control line's slight optical
# heaviness. Only EB Garamond weight and tracking vary. Wording, punctuation,
# 10.5/16 and 8pt/12pt title-matter spacing remain fixed.
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
# context-specimen.tex still loads the Phase-I candidate packages so that the
# first-page source remains one shared controlled environment.
need_tex cinzel.sty cinzel
need_tex marcellus.sty marcellus
need_tex CormorantGaramond.sty cormorantgaramond

if ! command -v xelatex >/dev/null 2>&1; then
  printf '%s\n' 'E289 Phase I.5: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi

if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.5: missing TeX Live components:'
  printf '  %s\n\n' "$missing"
  printf '%s\n' 'Install them once with:'
  printf '  sudo tlmgr update --self\n'
  printf '  sudo tlmgr install%s\n' "$missing"
  exit 2
fi

rm -f phase15-*.pdf

build_one() {
  variant=$1
  tracking=$2
  job=$3
  src="\\def\\EpigraphVariant{$variant}\\def\\EpigraphTracking{$tracking}\\input{context-specimen.tex}"

  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

# Variant 0 = EB Garamond Medium; variant 6 = EB Garamond Regular.
# The Medium ladder asks whether more air alone supplies the missing lift.
build_one 0 8  phase15-00-medium-ls08
build_one 0 9  phase15-01-medium-ls09
build_one 0 10 phase15-02-medium-ls10
build_one 0 11 phase15-03-medium-ls11
# The Regular pair tests whether the perceived solidity comes primarily from
# stroke weight rather than spacing. Keep this deliberately narrow at 8/9.
build_one 6 8  phase15-04-regular-ls08
build_one 6 9  phase15-05-regular-ls09

printf '\nBuilt Phase I.5 proofs:\n'
printf '  %s\n' \
  phase15-00-medium-ls08.pdf \
  phase15-01-medium-ls09.pdf \
  phase15-02-medium-ls10.pdf \
  phase15-03-medium-ls11.pdf \
  phase15-04-regular-ls08.pdf \
  phase15-05-regular-ls09.pdf
