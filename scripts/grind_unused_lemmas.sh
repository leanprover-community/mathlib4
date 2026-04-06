#!/usr/bin/env bash
# Usage: ./scripts/grind_unused_lemmas.sh [N] [logfile]
#
# Builds Mathlib with `set_option grind.unusedLemmaThreshold N` (default 10)
# and reports which E-matching lemmas are activated >= N times but unused in proofs.
#
# If a logfile is given as the second argument, skips the build and processes that log instead.
# Output is written to grind-unused-lemmas.md.
#
# Requires a Lean toolchain that supports grind.unusedLemmaThreshold
# (leanprover/lean4#12805 or later).

set -euo pipefail

THRESHOLD="${1:-10}"
LOGFILE="${2:-}"
OUTFILE="grind-unused-lemmas.md"
LAKEFILE="lakefile.lean"
OPTION_LINE="  ⟨\`grind.unusedLemmaThreshold, .ofNat $THRESHOLD⟩,"

if [ -z "$LOGFILE" ]; then
  LOGFILE="/tmp/mathlib-grind-threshold-build.log"

  # Patch lakefile to add the option (in mathlibOnlyLinters, which uses weak prefix)
  if grep -q 'grind.unusedLemmaThreshold' "$LAKEFILE"; then
    # Update existing threshold value
    sed -i "s/⟨\`grind.unusedLemmaThreshold, .ofNat [0-9]*⟩/⟨\`grind.unusedLemmaThreshold, .ofNat $THRESHOLD⟩/" "$LAKEFILE"
  else
    # Insert after linter.style.longFile line
    sed -i "/linter.style.longFile/a\\$OPTION_LINE" "$LAKEFILE"
  fi

  echo "Building Mathlib with grind.unusedLemmaThreshold=$THRESHOLD..."
  lake build Mathlib -q --log-level=info 2>&1 | tee "$LOGFILE"

  # Remove the option from lakefile after building
  sed -i '/grind.unusedLemmaThreshold/d' "$LAKEFILE"
fi

echo "Processing $LOGFILE..."

# Extract (file, lemma) pairs from warning blocks, deduplicate, count files per lemma
TABLE=$(awk '
/^warning:.*unused E-matching/ { split($2, a, ":"); file = a[1] }
/^\s+\[thm\]/ {
    lemma = $0
    gsub(/.*\[thm\] /, "", lemma)
    gsub(/ ↦.*/, "", lemma)
    print file "\t" lemma
}' "$LOGFILE" | sort -u | awk -F'\t' '{print $2}' | sort | uniq -c | sort -rn)

TOTAL_WARNINGS=$(grep -c "unused E-matching" "$LOGFILE" || true)
TOTAL_LEMMAS=$(echo "$TABLE" | wc -l)

cat > "$OUTFILE" <<EOF
# Unused E-matching lemmas in Mathlib (\`grind.unusedLemmaThreshold $THRESHOLD\`)

Lemmas that are activated ${THRESHOLD}+ times by \`grind\` but do not appear in the final proof term,
grouped by how many distinct files they appear in.

## By number of files affected

| Files | Lemma |
|------:|-------|
EOF

echo "$TABLE" | while read -r count lemma; do
  echo "| $count | \`$lemma\` |"
done >> "$OUTFILE"

cat >> "$OUTFILE" <<EOF

## Notes

- $TOTAL_WARNINGS total warning sites across $TOTAL_LEMMAS distinct lemmas.
EOF

echo "Wrote $OUTFILE"
