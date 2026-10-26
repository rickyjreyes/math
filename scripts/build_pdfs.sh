#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$ROOT/.build"
cd "$ROOT"
count=0
for src in papers/*/main.tex; do
  slug="$(basename "$(dirname "$src")")"
  out="$ROOT/.build/$slug"
  mkdir -p "$out" "$ROOT/preprints/$slug"
  echo "Compiling $slug"
  ( cd "$(dirname "$src")"
    pdflatex -halt-on-error -file-line-error -interaction=nonstopmode -output-directory="$out" main.tex >"$out/pass1.log" 2>&1 || { tail -100 "$out/pass1.log"; exit 1; }
    pdflatex -halt-on-error -file-line-error -interaction=nonstopmode -output-directory="$out" main.tex >"$out/pass2.log" 2>&1 || { tail -100 "$out/pass2.log"; exit 1; }
  )
  test -s "$out/main.pdf"
  cp "$out/main.pdf" "$ROOT/preprints/$slug/paper.pdf"
  count=$((count + 1))
done
test "$count" -eq 14
pdflatex -halt-on-error -file-line-error -interaction=nonstopmode -output-directory="$ROOT/.build" overview.tex >"$ROOT/.build/overview-pass1.log" 2>&1 || { tail -100 "$ROOT/.build/overview-pass1.log"; exit 1; }
pdflatex -halt-on-error -file-line-error -interaction=nonstopmode -output-directory="$ROOT/.build" overview.tex >"$ROOT/.build/overview-pass2.log" 2>&1 || { tail -100 "$ROOT/.build/overview-pass2.log"; exit 1; }
cp "$ROOT/.build/overview.pdf" "$ROOT/overview.pdf"
test -s "$ROOT/overview.pdf"
echo "Produced $count PDFs and overview.pdf"
