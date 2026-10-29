#!/usr/bin/env bash
set -euo pipefail
manuscript_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$manuscript_directory"
mkdir -p build
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build manuscript.tex
cp -- build/manuscript.pdf manuscript.pdf
