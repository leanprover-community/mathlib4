#!/bin/bash

# Group logging using the ::group:: workflow command
echo "::group::Elan Installation Output"

set -o pipefail
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf |
  sh -s -- -y --default-toolchain none
rm -f elan-init

echo "$HOME/.elan/bin" >>"$GITHUB_PATH"
"$HOME"/.elan/bin/lean --version
"$HOME"/.elan/bin/lake --version

echo "::endgroup::"
echo
