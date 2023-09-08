#!/usr/bin/env bash

set -exo pipefail

sudo apt install -y git curl

# Note that we're using `-y` here,
# unlike the standard `curl [...] -sSf | sh` installation method.
wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh

# The following test is needed in case VScode or VSCodium was installed by other
# means (e.g. using Ubuntu snap)
vsc="$(which code 2>/dev/null || which codium 2>/dev/null)"
if [ -z "$vsc" ]; then
  wget -O code.deb https://go.microsoft.com/fwlink/?LinkID=760868
  sudo apt install -y ./code.deb
  rm code.deb
  vsc=code
fi

# Install the Lean4 VS Code extension
"$vsc" --install-extension leanprover.lean4

. ~/.profile
