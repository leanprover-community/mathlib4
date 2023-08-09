#!/usr/bin/env bash

set -e
set -o pipefail

if [ ! -d Mathlib ] ; then
    echo "No Mathlib/ directory; are you at the root of the mathlib4 repo?"
    exit 1
fi

if [ ! $1 ] ; then
    echo "usage: ./scripts/start_port.sh Mathlib/Foo/Bar/Baz.lean"
    exit 1
fi

# arguments
root_path="$(pwd)"
mathlib4_path="$1"

case $mathlib4_path in
    Mathlib/*) true ;;
    Archive/*) true ;;
    Counterexamples/*) true ;;
    *) echo "argument must begin with Mathlib/, Archive/, or Counterexamples/"
       exit 1 ;;
esac

MATHLIB3PORT_BASE_URL=https://raw.githubusercontent.com/leanprover-community/mathlib3port/master
LEAN3PORT_BASE_URL=https://raw.githubusercontent.com/leanprover-community/lean3port/master
PORT_STATUS_YAML=https://raw.githubusercontent.com/wiki/leanprover-community/mathlib/mathlib4-port-status.md

# process path name
mathlib4_mod=$(basename $(echo "$mathlib4_path" | tr / .) .lean)
mathlib4_mod_tail=${mathlib4_mod#Mathlib.}
mathlib3port_url=$MATHLIB3PORT_BASE_URL/${1/#Mathlib/Mathbin}
lean3port_url=$LEAN3PORT_BASE_URL/${1/#Mathlib/Leanbin}

# start the port from the latest master
git fetch
BASE_BRANCH=${BASE_BRANCH=origin/master}
BASE_COMMIT=$(git rev-parse $BASE_BRANCH)

TMP_DIR=$(mktemp -d)
trap 'rm -fr "$TMP_DIR"' 0 1 2 13 15

export GIT_WORK_TREE=$TMP_DIR/working_tree
export GIT_INDEX_FILE=$TMP_DIR/index
mkdir -p "$GIT_WORK_TREE"

echo "Checking out a new branch in a temporary working tree"
git ls-tree -z -r --full-name "$BASE_COMMIT" | git update-index -z --index-info
git checkout-index -a

echo "Downloading latest version from mathlib3port"
(
    cd $GIT_WORK_TREE;
    # download the file, but don't commit it yet
    mkdir -p "$(dirname "$mathlib4_path")"
    curl --silent --show-error --fail -o "$mathlib4_path" "$lean3port_url" || curl --silent --show-error --fail -o "$mathlib4_path" "$mathlib3port_url"
)

# Empty commit with nice title. Used by gh and hub to suggest PR title.
BASE_COMMIT="$(echo "feat: port $mathlib4_mod_tail" | git commit-tree "$(git write-tree)" -p "$BASE_COMMIT")"

# Add the mathport file
git update-index --add "$mathlib4_path"
BASE_COMMIT="$(echo "Initial file copy from mathport" | git commit-tree "$(git write-tree)" -p "$BASE_COMMIT")"

echo "Applying automated fixes"
# Apply automated fixes

pushd $GIT_WORK_TREE;
sed -i 's/Mathbin\./Mathlib\./g' "$mathlib4_path"
sed -i 's/Leanbin\./Mathlib\./g' "$mathlib4_path"
sed -i '/^import/{s/[.]Gcd/.GCD/g; s/[.]Modeq/.ModEq/g; s/[.]Nary/.NAry/g; s/[.]Peq/.PEq/g; s/[.]Pfun/.PFun/g; s/[.]Pnat/.PNat/g; s/[.]Smul/.SMul/g; s/[.]Zmod/.ZMod/g; s/[.]Nnreal/.NNReal/g; s/[.]Ennreal/.ENNReal/g}' "$mathlib4_path"

python3 "$root_path/scripts/fix-line-breaks.py" "$mathlib4_path" "$mathlib4_path.tmp"
mv "$mathlib4_path.tmp" "$mathlib4_path"

if [[ "$mathlib4_mod" =~ ^Mathlib. ]]; then
    which_all=Mathlib
elif [[ "$mathlib4_mod" =~ ^Counterexamples. ]]; then
    which_all=Counterexamples
elif [[ "$mathlib4_mod" =~ ^Archive. ]]; then
    which_all=Archive
fi
(echo "import $mathlib4_mod" ; cat $which_all.lean) | LC_ALL=C sort | uniq > $which_all.lean.tmp
mv -f $which_all.lean.tmp $which_all.lean

popd

# Commit them
git update-index --add $which_all.lean
git update-index --add "$mathlib4_path"
BASE_COMMIT="$(git commit-tree "$(git write-tree)" -p "$BASE_COMMIT" << EOF
automated fixes

Mathbin -> Mathlib
fix certain import statements
move "by" to end of line
add import to $which_all.lean
EOF
)"

echo "Successfully created initial commits:"
git log -n3 $BASE_COMMIT --graph --oneline
echo ""

mathlib3_module=$(grep '^! .*source module ' <"$GIT_WORK_TREE/$mathlib4_path" | sed 's/.*source module \(.*\)$/\1/')

# stop using the temporary working tree
unset GIT_WORK_TREE
unset GIT_INDEX_FILE

if git cat-file -e origin/master:$mathlib4_path 2> /dev/null; then
    echo "WARNING: this file has already been ported!"
    echo "To continue anyway with a fresh port, you can run"
    echo ""
    echo "    git checkout $BASE_COMMIT -b port/${mathlib4_mod_tail}-again"
    echo ""
    exit 1
fi

if PR=$(curl --silent --show-error --fail "$PORT_STATUS_YAML" | grep -F "$mathlib3_module: " | grep -o -E "mathlib4#[0-9]+"); then
    set +x
    echo "WARNING: The file is already in the process of being ported in $PR."
    echo "To continue anyway with a fresh port, you can run"
    echo ""
    echo "    git checkout $BASE_COMMIT -b port/${mathlib4_mod_tail}-<some-suffix>"
    echo ""
    exit 1
fi

branch_name=port/${mathlib4_mod_tail}
echo "Checking out a new $branch_name branch from $BASE_COMMIT"
git checkout --no-track -b "$branch_name" "$BASE_COMMIT"

echo "After pushing, you can open a PR at:"
echo "https://github.com/leanprover-community/mathlib4/compare/$branch_name?expand=1&title=feat:+port+$mathlib4_mod_tail&labels=mathlib-port"
