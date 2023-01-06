#!/usr/bin/env bash

set -e

if [ ! -d Mathlib ] ; then
    echo "No Mathlib/ directory; are you at the root of the mathlib4 repo?"
    exit 1
fi

if [ ! $1 ] ; then
    echo "usage: ./scripts/start_port.sh Mathlib/Foo/Bar/Baz.lean"
    exit 1
fi
    
if [ -f $1 ] ; then
    echo "file already exists"
    exit 1
fi

set -x
set -o pipefail

MATHLIB3PORT_BASE_URL=https://raw.githubusercontent.com/leanprover-community/mathlib3port/master
PORT_STATUS_YAML=https://raw.githubusercontent.com/wiki/leanprover-community/mathlib/mathlib4-port-status.md
TMP_FILE=start_port_tmp.lean

mathlib4_path=$1
mathlib4_mod=$(basename $(echo "$mathlib4_path" | tr / .) .lean)

mathlib3port_url=$MATHLIB3PORT_BASE_URL/Mathbin/${1#Mathlib/}

curl --silent --show-error -o "$TMP_FILE" "$mathlib3port_url"

mathlib3_module=$(grep '^! .*source module ' <"$TMP_FILE" | sed 's/.*source module \(.*\)$/\1/')

if curl --silent --show-error "$PORT_STATUS_YAML" | grep -F "$mathlib3_module: " | grep "mathlib4#" ; then
    set +x
    echo "WARNING: The file is already in the process of being ported."
    echo "(See line above for PR number.)"
    rm "$TMP_FILE"
    exit 1
fi

mkdir -p $(dirname "$mathlib4_path")
mv "$TMP_FILE" "$mathlib4_path"

git fetch
branch_name=port/${mathlib4_mod#Mathlib.}
git checkout --no-track -b "$branch_name" origin/master

git add "$mathlib4_path"
git commit -m 'Initial file copy from mathport'

sed -i 's/Mathbin\./Mathlib\./g' "$mathlib4_path"

(echo "import $mathlib4_mod" ; cat Mathlib.lean) | LC_ALL=C sort > Mathlib.lean.tmp
mv -f Mathlib.lean.tmp Mathlib.lean

git add Mathlib.lean "$mathlib4_path"
git commit -m 'Mathbin -> Mathlib; add import to Mathlib.lean'
