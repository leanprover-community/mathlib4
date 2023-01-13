#!/usr/bin/env bash

grep -lr "^  by\$" Mathlib | xargs -n 1 awk -i inplace '{do {{if (match($0, "^  by$") && length(p) < 98 && (!(match(p, "^[ \t]*--.*$")))) {p=p " by";} else {if (NR!=1) {print p}; p=$0}}} while (getline == 1) if (getline==0) print p}'
