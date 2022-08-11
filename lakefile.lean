import Lake

open Lake DSL

package mathlib

@[defaultTarget]
lean_lib Mathlib

@[defaultTarget]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
