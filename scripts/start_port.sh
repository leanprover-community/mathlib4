#!/usr/bin/env bash

set -e

if [ ! -d Mathlib ] ; then
    echo "No Mathlib/ directory; are you at the root of the mathlib4 repo?"
    exit 1
fi

if [ ! $1 ] ; then
    echo "usage: ./scripts/start_port.sh [--restart] Mathlib/Foo/Bar/Baz.lean"
    exit 1
fi

POSITIONAL_ARGS=()
RESTART=

while [[ $# -gt 0 ]]; do
    case $1 in
        -r|--restart)
            RESTART=1
            shift
            ;;
        -*|--*)
            echo "Unknown option $1"
            exit 1
            ;;
        *)
            POSITIONAL_ARGS+=("$1") # save positional arg
            shift # past argument
            ;;
    esac
done
set -- "${POSITIONAL_ARGS[@]}" # restore positional parameters

case $1 in
    Mathlib/*) true ;;
    *) echo "argument must begin with Mathlib/"
       exit 1 ;;
esac

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

curl --silent --show-error --fail -o "$TMP_FILE" "$mathlib3port_url"

mathlib3_module=$(grep '^! .*source module ' <"$TMP_FILE" | sed 's/.*source module \(.*\)$/\1/')

if ![ "$RESTART" ] && curl --silent --show-error --fail "$PORT_STATUS_YAML" | grep -F "$mathlib3_module: " | grep "mathlib4#" ; then
    set +x
    echo "WARNING: The file is already in the process of being ported."
    echo "(See line above for PR number.)"
    rm "$TMP_FILE"
    exit 1
fi

mkdir -p $(dirname "$mathlib4_path")
mv "$TMP_FILE" "$mathlib4_path"

git fetch
mathlib4_mod_tail=${mathlib4_mod#Mathlib.}
if [ "$RESTART" ]; then
    old_branch_name=port/${mathlib4_mod_tail}
    branch_name=port/tmp/${mathlib4_mod_tail}
else
    branch_name=port/${mathlib4_mod_tail}
fi
git checkout --no-track -b "$branch_name" origin/master

# Empty commit with nice title. Used by gh and hub to suggest PR title.
git commit -m "feat: port $mathlib4_mod_tail" --allow-empty

git add "$mathlib4_path"
git commit -m 'Initial file copy from mathport'

sed -i 's/Mathbin\./Mathlib\./g' "$mathlib4_path"
sed -i '/^import/{s/[.]Gcd/.GCD/g; s/[.]Modeq/.ModEq/g; s/[.]Nary/.NAry/g; s/[.]Peq/.PEq/g; s/[.]Pfun/.PFun/g; s/[.]Pnat/.PNat/g; s/[.]Smul/.SMul/g; s/[.]Zmod/.ZMod/g}' "$mathlib4_path"

# awk script taken from https://github.com/leanprover-community/mathlib4/pull/1523
awk '{do {{if (match($0, "^  by$") && length(p) < 98 && (!(match(p, "^[ \t]*--.*$")))) {p=p " by";} else {if (NR!=1) {print p}; p=$0}}} while (getline == 1) if (getline==0) print p}' "$mathlib4_path" > "$mathlib4_path.tmp"
mv "$mathlib4_path.tmp" "$mathlib4_path"

(echo "import $mathlib4_mod" ; cat Mathlib.lean) | LC_ALL=C sort | uniq > Mathlib.lean.tmp
mv -f Mathlib.lean.tmp Mathlib.lean

git add Mathlib.lean "$mathlib4_path"
git commit \
	-m 'automated fixes' \
	-m '' \
	-m 'Mathbin -> Mathlib' \
	-m 'fix certain import statements' \
	-m 'move "by" to end of line' \
	-m 'add import to Mathlib.lean'

set +x

if [ "$RESTART" ]; then
    LAST_PORT_COMMIT=$(git rev-list "$old_branch_name" ^origin/master --grep="automated fixes" | head -n1)
    # create a no-op merge commit with the previous auto-port, to aid with porting manual changes.
    # note that `-s ours` doesn't actually ensure nothing changes, so we do a checkout for good
    # measure
    git merge -s ours "$LAST_PORT_COMMIT" --no-commit
    git checkout HEAD -- .
    git commit -m "merge in previous autoported output"
    echo "# The script just created a branch $branch_name. You may want to:"
    echo "git checkout $old_branch_name"
    echo "git merge $branch_name"
    echo "git reset --soft $branch_name^   # the ^ is important to discard the merge commit"
    echo "git add -p # to manually discard/stage diff chunks"
else
    echo "After pushing, you can open a PR at:"
    echo "https://github.com/leanprover-community/mathlib4/compare/$branch_name?expand=1&title=feat:+port+$mathlib4_mod_tail&labels=mathlib-port"
fi
