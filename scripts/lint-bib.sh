#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

set -x

# Test if there are keys with characters outside alphanumeric, '-', '_', and ':'.
bibtool --pass.comments=on -- 'select{$key "[^-:A-Za-z0-9_]+"}' \
  docs/references.bib -o docs/non-ascii.bib.tmp

if [ -s docs/non-ascii.bib.tmp ]; then
  echo "::error:: There are items in references.bib with keys containing characters" \
    "outside alphanumeric, '-', '_', and ':':"
  cat docs/non-ascii.bib.tmp && rm docs/non-ascii.bib.tmp && exit 1
else
  rm docs/non-ascii.bib.tmp
fi

# https://leanprover-community.github.io/contribute/doc.html#citing-other-works
cp docs/references.bib docs/references.bib.old
bibtool --preserve.key.case=on --preserve.keys=on --pass.comments=on --print.use.tab=off -s \
  -i docs/references.bib -o docs/references.bib
diff -U8 docs/references.bib.old docs/references.bib
