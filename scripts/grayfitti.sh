#!/usr/bin/env bash

set -e -o pipefail

# Usage block
if [ $# -ne 1 ]; then
	echo "Usage: grayfitti.sh <filter>"
	echo "  <filter> is a string that filters the files to check"
	exit 1
fi

FILTER=$1

LEANFILES=$(git ls-files | grep "$FILTER")
MODNAMES=$(echo $LEANFILES | sed -e 's/\.lean//g' | sed -e 's/\//./g')

echo "Checking grayfitti for filter: $FILTER"
echo "Number of files: $(echo $MODNAMES | wc -w)"
echo

for file in $MODNAMES; do
	echo -n "Grayfitti: $file "
	# Generate the graph, write errors to /dev/null
	lake exe graph --to $file ~/tmp/tmp.xdot_json 2>/dev/null
	GRAY=$((grep e0e0e0 ~/tmp/tmp.xdot_json || true) | wc -l)
	TOTAL=$((grep Mathlib ~/tmp/tmp.xdot_json || true) | wc -l)
	PERCENT=0
	if [ $TOTAL -gt 0 ]; then
		PERCENT=$((100 * $GRAY / $TOTAL))
	fi
	echo "$PERCENT%"
done
