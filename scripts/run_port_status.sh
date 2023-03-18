#!/usr/bin/env bash

set -ex

[ -d port-repos ] || exit 1

git fetch origin
git rebase origin/master

function clone_pull {
    git clone "$2" $1 || true
    (cd $1 && git pull)
}

(cd port-repos &&
     clone_pull mathlib git@github.com:leanprover-community/mathlib.git &&
     clone_pull mathlib.wiki git@github.com:leanprover-community/mathlib.wiki.git)

./scripts/make_port_status.py

(cd port-repos/mathlib.wiki && git pull --rebase &&
     cp ../../port_status.yaml mathlib4-port-status.md &&
     cp ../../port_status_new.yaml mathlib4-port-status-yaml.md &&
     git commit -am 'Updated mathlib4 port status (markdown)' && git push)
