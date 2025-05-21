#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

set -x

# Install elan using the official script
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Load the new elan PATH
source ~/.elan/env

# Set the default Lean version to the latest stable release
elan toolchain install stable
elan default stable

# Check if VS Code is available on the command line
if ! command -v code &> /dev/null; then
    # Install the universal darwin build of VS Code
    curl -L https://update.code.visualstudio.com/latest/darwin-universal/stable -o ~/Downloads/VSCode-darwin-universal.zip

    # Unzip the downloaded file to the Applications folder
    unzip -o ~/Downloads/VSCode-darwin-universal.zip -d /Applications

    # Add the VS Code binary to the PATH to enable launching from the terminal
    cat >> ~/.zprofile << EOF
# Add Visual Studio Code (code)
export PATH="\$PATH:/Applications/Visual Studio Code.app/Contents/Resources/app/bin"
EOF

    # Load the new VS Code PATH
    source ~/.zprofile
else
    echo "VS Code is already installed."
fi

# Install the Lean4 VS Code extension
code --install-extension leanprover.lean4
