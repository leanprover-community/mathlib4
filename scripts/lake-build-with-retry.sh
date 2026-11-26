#!/bin/bash
# Script to run lake build on one or more targets until --no-build succeeds
# Usage: ./lake-build-with-retry.sh <target_name>...
# The environment variable MAX_TRIES bounds the attempts (default: 5).
#
# In the build job of .github/workflows/build_template.yml,
# this script MUST be run after cd-ing into pr-branch/,
# since we tell lake-build-wrapper.py to save a file to .lake/
# relative to the current working directory,
# as only that path is writable in our landrun sandbox.

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

TARGETS=("$@")
MAX_TRIES="${MAX_TRIES:-5}"
SCRIPTS_DIR="$(dirname "$(realpath "$0")")"

if [ ${#TARGETS[@]} -eq 0 ]; then
  echo "Usage: $0 <target_name>..."
  echo "Example: $0 Archive Counterexamples Wanted"
  exit 1
fi

# The build summary is named after the targets, joined with underscores.
SUMMARY_FILE=".lake/build_summary_$(IFS=_; echo "${TARGETS[*]}").json"
TARGETS_TEXT="$(IFS=' '; echo "${TARGETS[*]}")"

echo "Building $TARGETS_TEXT with up to $MAX_TRIES attempts..."

counter=0
while true; do
  counter=$((counter + 1))

  echo "**** start of lake build: attempt $counter"
  LEAN_ABORT_ON_PANIC=1 "${SCRIPTS_DIR}/lake-build-wrapper.py" "$SUMMARY_FILE" lake build --wfail -KCI "${TARGETS[@]}"
  echo "**** end of lake build: attempt $counter"

  echo "::group::lake build --no-build: attempt $counter"
  set +e
  lake build --no-build -v "${TARGETS[@]}"
  result=$?
  set -e
  echo "::endgroup::"

  if [ "$result" -eq 0 ]; then
    echo "lake build --no-build succeeded!"
    exit 0
  fi

  if [ "$counter" -ge "$MAX_TRIES" ]; then
    echo "Failed to build good oleans for $TARGETS_TEXT after $MAX_TRIES attempts!"
    exit 1
  fi
done
