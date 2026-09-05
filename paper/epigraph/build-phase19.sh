#!/bin/sh
set -eu

# Phase I.9: optical plaque-field size gate.
# Family/weight, tracking, wording, punctuation and size/leading are fixed.
# We preserve the empirically inferred optical-centering relation
#   pre-space = post-space + 2 pt
# and vary only the absolute size of the surrounding white-space field.
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
  printf '%s\n' 'E289 Phase I.9: xelatex is not available.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi

if [ -n "$missing" ]; then
  printf '%s\n' 'E289 Phase I.9: missing TeX Live components:'
  printf '  %s\n\n' "$missing"
  printf '%s\n' 'Install them once with:'
  printf '  sudo tlmgr update --self\n'
  printf '  sudo tlmgr install%s\n' "$missing"
  exit 2
fi

rm -f phase19-*.pdf

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

# All candidates preserve the same optical-centering offset (pre = post + 2).
# 14/12 is the anchor: it keeps the original 12pt epigraph-to-abstract spacing
# while widening the upper field to the same visible optical distance.
build_one 12 10 phase19-pre12-post10
build_one 13 11 phase19-pre13-post11
build_one 14 12 phase19-pre14-post12
build_one 15 13 phase19-pre15-post13
build_one 16 14 phase19-pre16-post14

printf '\nBuilt Phase I.9 source proofs:\n'
printf '  %s\n' \
  phase19-pre12-post10.pdf \
  phase19-pre13-post11.pdf \
  phase19-pre14-post12.pdf \
  phase19-pre15-post13.pdf \
  phase19-pre16-post14.pdf
