#!/usr/bin/env bash

set -exo pipefail

# Install Homebrew
set -e

if ! which brew > /dev/null; then
    # Install Homebrew
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install.sh)"
else
    # Update it, in case it has been ages since it's been updated
    brew update
fi

brew install elan
elan toolchain install stable
elan default stable

# Install and configure VS Code
if ! which code > /dev/null; then
    brew install --cask visual-studio-code
fi
code --install-extension leanprover.lean4
