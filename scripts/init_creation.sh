#!/usr/bin/env bash

 : <<'BASH_MODULE_DOC'

These are the commands to generate a "root" `Mathlib/Init.lean` file, imported by all the
`Mathlib` files that do not import any `Mathlib` file.

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

printf 'Creating `Mathlib/Init.lean`.\n'

# Creates the `Mathlib/Init.lean` files.
echo '-- This is the root file in Mathlib: it is imported by virtually *all* Mathlib files' > Mathlib/Init.lean

printf $'Don\'t forget to add `Mathlib.Init` to the `ignoreImport` field of `scripts/noshake.json`
This ensures that `import Mathlib.Init` does not trigger a `shake` exception.\n'
