#!/usr/bin/env bash

set -exo pipefail

sudo apt install -y git curl
# The following test is needed in case VScode or VSCodium was installed by other
# means (e.g. using Ubuntu snap)
vsc="$(which code || which codium)"
if [ -z "$vsc" ]; then
  wget -O code.deb https://go.microsoft.com/fwlink/?LinkID=760868
  sudo apt install -y ./code.deb
  rm code.deb
  vsc=code
fi
"$vsc" --install-extension leanprover.lean4
wget https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh
bash elan-init.sh -y
rm elan-init.sh
. ~/.profile
