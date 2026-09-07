#!/bin/sh
set -eu
cd "$(dirname "$0")"

PUBLIC_PDF='Reciprocal Sums over Separated Integer Intervals.pdf'

latexmk -xelatex -interaction=nonstopmode -halt-on-error main.tex
cp -f main.pdf "$PUBLIC_PDF"
printf 'Built %s\n' "$PUBLIC_PDF"
