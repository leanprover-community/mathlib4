#!/usr/bin/env bash
# Times `runLinter Mathlib` with four Batteries variants on one machine.
# Usage (from the Mathlib root, with the Mathlib cache in place): scripts/lint-bench/run.sh [rounds]
#
#   base     Batteries as in lake-manifest.json
#   env      + persistent imported environment (runLinter.env.lean.in)
#   workers  + bounded lint worker pool (Frontend.workers.lean.in)
#   both     + both changes
#
# The order of the variants rotates each round.
set -euo pipefail
rounds=${1:-3}
here=$(cd "$(dirname "$0")" && pwd)
bench=.lake/lint-bench
cfgs=(base env workers both)

rm -rf "$bench"
mkdir -p "$bench"
for c in "${cfgs[@]}"; do
  cp -a .lake/packages/batteries "$bench/$c"
  if [[ $c == env || $c == both ]]; then
    cp "$here/runLinter.env.lean.in" "$bench/$c/scripts/runLinter.lean"
  fi
  if [[ $c == workers || $c == both ]]; then
    cp "$here/Frontend.workers.lean.in" "$bench/$c/Batteries/Tactic/Lint/Frontend.lean"
  fi
  (cd "$bench/$c" && lake build runLinter 2>&1 | tail -1)
done
sha256sum "$bench"/*/.lake/build/bin/runLinter
echo "nproc=$(nproc)"
free -g || true

# Runs a command with output to $2 and writes "wall user sys max_rss_kib" to $1.
timed() {
  local tf=$1 log=$2
  shift 2
  if [[ -x /usr/bin/time ]]; then
    /usr/bin/time -f "%e %U %S %M" -o "$tf" "$@" > "$log" 2>&1
  else
    local TIMEFORMAT='%R %U %S 0'
    { time "$@" > "$log" 2>&1; } 2> "$tf"
  fi
}

for r in $(seq 1 "$rounds"); do
  k=$(( (r - 1) % ${#cfgs[@]} ))
  order=("${cfgs[@]:k}" "${cfgs[@]:0:k}")
  for c in "${order[@]}"; do
    out=$bench/$c-$r
    status=0
    timed "$out.time" "$out.log" env LEAN_ABORT_ON_PANIC=1 \
      lake env "$bench/$c/.lake/build/bin/runLinter" --no-build --trace Mathlib || status=$?
    read -r wall user sys rss < <(tail -1 "$out.time")
    # A digest of the per-linter results, to check that all variants agree.
    results=$({ grep -E "Passed!|Failed with" "$out.log" || true; } | sed 's/^.*- //' | sort | sha256sum | cut -c1-12)
    echo "BENCH round=$r cfg=$c exit=$status wall=$wall user=$user sys=$sys rss_mib=$((rss / 1024)) results=$results"
  done
done

echo "Median wall time (s) per variant:"
for c in "${cfgs[@]}"; do
  for r in $(seq 1 "$rounds"); do
    tail -1 "$bench/$c-$r.time" | cut -d' ' -f1
  done | sort -n | awk -v c="$c" '{a[NR] = $1} END {print c, a[int((NR + 1) / 2)]}'
done
