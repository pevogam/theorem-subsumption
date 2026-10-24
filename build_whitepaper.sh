#!/usr/bin/env bash

set -euo pipefail

# Canonical source file
SRC="${1:-whitepaper.md}"

if [[ ! -f "$SRC" ]]; then
  echo "Error: Markdown source not found: $SRC" >&2
  exit 1
fi

# Remove the final extension while preserving any path.
BASE="${SRC%.*}"

PDF="${BASE}.pdf"
DOCX="${BASE}.docx"

PANDOC_FROM="markdown+yaml_metadata_block+tex_math_dollars+pipe_tables+fenced_code_blocks"

# Check required tools.
if ! command -v pandoc >/dev/null 2>&1; then
  echo "Error: pandoc is required but was not found in PATH." >&2
  exit 1
fi

if ! command -v weasyprint >/dev/null 2>&1; then
  echo "Error: weasyprint is required for PDF generation but was not found in PATH." >&2
  exit 1
fi

echo "Source: $SRC"

echo "Building PDF..."
pandoc "$SRC" \
  --standalone \
  --from="$PANDOC_FROM" \
  --to=html5 \
  --mathml \
  --pdf-engine=weasyprint \
  -o "$PDF"

echo "Created: $PDF"

echo "Building DOCX..."
pandoc "$SRC" \
  --standalone \
  --from="$PANDOC_FROM" \
  --to=docx \
  -o "$DOCX"

echo "Created: $DOCX"

echo
echo "Build complete."
