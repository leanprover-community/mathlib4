#!/usr/bin/env bash

set -exo pipefail

# Install Homebrew
if ! which brew > /dev/null; then
    # Install Homebrew
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"
else
    # Update it, in case it has been ages since it's been updated
    brew update
fi

curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
elan toolchain install stable
elan default stable

# Install and configure VS Code
if ! which code > /dev/null; then
    brew install --cask visual-studio-code
fi

# Install the Lean4 VS Code extension
code --install-extension leanprover.lean4
