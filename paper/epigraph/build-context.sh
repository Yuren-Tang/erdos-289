#!/bin/sh
set -eu

# Build seven context proofs. Run from paper/epigraph or from any directory.
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$HERE"

TEXMFHOME=${TEXMFHOME:-/tmp/e289-empty-texmf}
export TEXMFHOME
mkdir -p "$TEXMFHOME"

# BasicTeX is intentionally small. Before starting the proof matrix, detect
# all TeX Live components used by the real E289 first-page environment and by
# the isolated legacy Trajan reference assets.
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
need_tex trajan.sty trajan
need_tex soul.sty soul
need_tex standalone.cls standalone
need_tex microtype.sty microtype
need_tex enumitem.sty enumitem
need_tex csquotes.sty csquotes
need_tex biblatex.sty biblatex
need_tex hyperref.sty hyperref
need_tex cinzel.sty cinzel
need_tex marcellus.sty marcellus
need_tex CormorantGaramond.sty cormorantgaramond

if ! command -v pdflatex >/dev/null 2>&1; then
  printf '%s\n' 'E289 context proof: pdflatex is not available in this TeX installation.' >&2
  exit 2
fi
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

# TeX Live Trajan is legacy Type 1/METAFONT. Render two literal-text reference
# assets with pdfLaTeX+soul: 0.08 em reproduces the current E289 manuscript;
# 0.09 em normalizes Trajan to the current successful E306 LetterSpace=9 gate.
rm -f trajan-control-08.pdf trajan-control-09.pdf context-*.pdf
pdflatex -interaction=nonstopmode -halt-on-error \
  -jobname=trajan-control-08 trajan-control-asset.tex
pdflatex -interaction=nonstopmode -halt-on-error \
  -jobname=trajan-control-09 \
  '\def\TrajanNormalized{1}\input{trajan-control-asset.tex}'

build_one() {
  variant=$1
  job=$2
  src="\\def\\EpigraphVariant{$variant}\\input{context-specimen.tex}"

  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  biber "$job"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
  xelatex -interaction=nonstopmode -halt-on-error -jobname="$job" "$src"
}

# Variant 0 is historical reference only. Variants 1--6 are the normalized
# family/weight gate at the E306-current 0.09 em tracking target.
build_one 0 context-00-trajan-current-08
build_one 1 context-01-trajan-normalized-09
build_one 2 context-02-cinzel-regular
build_one 3 context-03-cinzel-bold
build_one 4 context-04-marcellus-regular
build_one 5 context-05-cormorant-medium
build_one 6 context-06-cormorant-semibold

printf '\nBuilt context proofs:\n'
printf '  %s\n' context-00-trajan-current-08.pdf \
  context-01-trajan-normalized-09.pdf \
  context-02-cinzel-regular.pdf \
  context-03-cinzel-bold.pdf \
  context-04-marcellus-regular.pdf \
  context-05-cormorant-medium.pdf \
  context-06-cormorant-semibold.pdf
