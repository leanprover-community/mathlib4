#!/bin/bash
# Script to run lake build on a target until --no-build succeeds
# Usage: ./lake-build-with-retry.sh <target_name> [max_tries, default: 5]

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

TARGET_NAME="$1"
MAX_TRIES="${2:-5}"
SCRIPTS_DIR="$(dirname "$(realpath "$0")")"

if [ -z "$TARGET_NAME" ]; then
  echo "Usage: $0 <target_name> [max_tries, default: 5]"
  echo "Example: $0 Mathlib 5"
  exit 1
fi

echo "Building $TARGET_NAME with up to $MAX_TRIES attempts..."

counter=0
while true; do
  counter=$((counter + 1))

  echo "::group::{lake build: attempt $counter}"
  bash -o pipefail -c "env LEAN_ABORT_ON_PANIC=1 $SCRIPTS_DIR/lake-build-wrapper.py lake build --wfail -KCI $TARGET_NAME"
  echo "::endgroup::"

  echo "::group::{lake build --no-build: attempt $counter}"
  set +e
  "$SCRIPTS_DIR/lake-build-wrapper.py" lake build --no-build -v "$TARGET_NAME"
  result=$?
  set -e
  echo "::endgroup::"

  if [ $result -eq 0 ]; then
    echo "lake build --no-build succeeded!"
    exit 0
  fi

  if [ $counter -ge $MAX_TRIES ]; then
    echo "Failed to build good oleans for $TARGET_NAME after $MAX_TRIES attempts!"
    exit 1
  fi
done
