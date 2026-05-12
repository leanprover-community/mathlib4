#!/usr/bin/env bash

set -euo pipefail

file="${1:-MathlibTest/IntegrabilityTactic.lean}"

if [[ ! -f "$file" ]]; then
  printf 'error: file not found: %s\n' "$file" >&2
  exit 1
fi

total=$( (rg -o '\bexample\b' "$file" || true) | wc -l | tr -d '[:space:]' )
failing=$( (rg -o -F 'fail_if_success fun_prop' "$file" || true) | wc -l | tr -d '[:space:]' )
passing=$((total - failing))

if (( passing < 0 )); then
  printf 'error: counted more failing tests than total tests (%s > %s)\n' "$failing" "$total" >&2
  exit 1
fi

perl -0pi -e 's|update by running: .*|update by running: `scripts/update-integrability-tactic-counts.sh`|' "$file"
perl -0pi -e "s|CURRENT PASSING TEST: .*|CURRENT PASSING TEST: $passing / $total|" "$file"

printf 'Integrability tactic tests: %s / %s passing (%s guarded by fail_if_success fun_prop)\n' \
  "$passing" "$total" "$failing"
