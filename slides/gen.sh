#!/usr/bin/env bash
# Usage:
#   ./slides/gen.sh slides/2026-03/sroof-talk.md        # default: html + png
#   ./slides/gen.sh slides/2026-03/sroof-talk.md pptx   # pptx only
#   ./slides/gen.sh slides/2026-03/sroof-talk.md all     # html + png + pptx

set -euo pipefail

INPUT="${1:-}"
FORMAT="${2:-default}"

if [[ -z "$INPUT" ]]; then
  echo "Usage: $0 <slides.md> [pptx|all]"
  exit 1
fi

BASE="${INPUT%.md}"
DIR="$(dirname "$INPUT")"

case "$FORMAT" in
  pptx)
    echo "→ PPTX"
    npx @marp-team/marp-cli@latest "$INPUT" --pptx -o "${BASE}.pptx"
    echo "✓ ${BASE}.pptx"
    ;;
  all)
    echo "→ HTML"
    npx @marp-team/marp-cli@latest "$INPUT" --html -o "${BASE}.html"
    echo "→ PNG"
    npx @marp-team/marp-cli@latest "$INPUT" --images png --output "${BASE}-slide"
    echo "→ PPTX"
    npx @marp-team/marp-cli@latest "$INPUT" --pptx -o "${BASE}.pptx"
    echo "✓ all done: ${DIR}/"
    ;;
  *)
    echo "→ HTML"
    npx @marp-team/marp-cli@latest "$INPUT" --html -o "${BASE}.html"
    echo "→ PNG"
    npx @marp-team/marp-cli@latest "$INPUT" --images png --output "${BASE}-slide"
    echo "✓ ${BASE}.html + ${BASE}-slide.NNN"
    ;;
esac
