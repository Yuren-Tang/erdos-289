#!/bin/sh
set -eu

# Build six real-first-page context proofs. Run from paper/epigraph or anywhere.
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"

TEXMFHOME=${TEXMFHOME:-/tmp/e289-empty-texmf}
export TEXMFHOME
mkdir -p "$TEXMFHOME"

# BasicTeX is intentionally small. Phase I is OpenType-only: the specified
# E306 EB Garamond Medium control plus free TeX Live candidates. Legacy Trajan
# is not a build dependency and therefore cannot block the comparison gate.
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
need_tex microtype.sty microtype
need_tex enumitem.sty enumitem
need_tex csquotes.sty csquotes
need_tex biblatex.sty biblatex
need_tex hyperref.sty hyperref
need_tex cinzel.sty cinzel
need_tex marcellus.sty marcellus
need_tex CormorantGaramond.sty cormorantgaramond

if ! command -v xelatex >/dev/null 2>&1; then
  printf '%s\n' 'E289 context proof: xelatex is not available in this TeX installation.' >&2
  exit 2
fi
if ! command -v biber >/dev/null 2>&1; then
  missing="$missing biber"
fi

if [ -n "$missing" ]; then
  printf '%s\n' 'E289 context proof: missing TeX Live components:'
  printf '  %s\n\n' "$missing"
  printf '%s\n' 'Install them once with:'
  printf '  sudo tlmgr update --self\n'
  printf '  sudo tlmgr install%s\n' "$missing"
  exit 2
fi

rm -f context-*.pdf

build_one() {
  variant=$1
  job=$2
  src="\\def\\EpigraphVariant{$variant}\\input{context-specimen.tex}"

  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

# Exact E306 typography control, then family/weight candidates. Every proof uses
# 10.5/16, LetterSpace=8 and 8pt/12pt vertical spacing.
build_one 0 context-00-e306-ebgaramond-medium
build_one 1 context-01-cinzel-regular
build_one 2 context-02-cinzel-bold
build_one 3 context-03-marcellus-regular
build_one 4 context-04-cormorant-medium
build_one 5 context-05-cormorant-semibold

printf '\nBuilt context proofs:\n'
printf '  %s\n' context-00-e306-ebgaramond-medium.pdf \
  context-01-cinzel-regular.pdf \
  context-02-cinzel-bold.pdf \
  context-03-marcellus-regular.pdf \
  context-04-cormorant-medium.pdf \
  context-05-cormorant-semibold.pdf
