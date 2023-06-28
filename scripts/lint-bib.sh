#!/usr/bin/env bash

set -exo pipefail
# https://leanprover-community.github.io/contribute/doc.html#citing-other-works
cp docs/references.bib docs/references.bib.old
bibtool --preserve.key.case=on --preserve.keys=on --pass.comments=on --print.use.tab=off -s \
  -i docs/references.bib -o docs/references.bib
diff -U8 docs/references.bib.old docs/references.bib
