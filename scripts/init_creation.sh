#!/usr/bin/env bash

 : <<'BASH_MODULE_DOC'

These are the commands to add an import of `Mathlib/Init.lean` to all `Mathlib` files
that do not import any `Mathlib` file.

BASH_MODULE_DOC

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

# `mathlibNonImportingFiles` generates the list of `Mathlib` files that do not have Mathlib imports.
# The output of `lake exe graph` are many lines like
# `  "Mathlib..." -> "Mathlib...";`
# using `"` as separator, the 2nd field is an imported module ("source") and
# the 4th field is a module that imports it ("target").
# so we want the sources that are not targets.
mathlibNonImportingFiles () {
lake exe graph |
  awk -F'"' '($4 ~ ".") { sources[$2]; targets[$4] }
    END{
      printf "for f in"
      for(t in sources) { if(!(t in targets)) {
        gsub(/\./, "/", t)
        print t".lean"
      } }
     }'
}

printf 'Adding `import Mathlib.Init` to all file that import no Mathlib file.\n'

# The `sed` command appends the line `import Mathlib.Init` after the first
# `-/[linebreaks]*` of each file printed by `mathlibNonImportingFiles`.
sed -i -z 's=-/\n*=&import Mathlib.Init\n=' $(mathlibNonImportingFiles)
