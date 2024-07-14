#!/usr/bin/env bash
# Modify all lean files in mathlib to put the "by" in lines that only contain "  by" at the end of the previous line,
# when the previous line with " by" appended is not longer than 100 characters.

grep -lr "^  by\$" Mathlib | xargs -n 1 awk -i inplace '{do {{if (match($0, "^  by$") && length(p) < 98 && (!(match(p, "^[ \t]*--.*$")))) {p=p " by";} else {if (NR!=1) {print p}; p=$0}}} while (getline == 1) if (getline==0) print p}'
