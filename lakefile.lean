import Lake

open Lake DSL

package mathlib

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := #["-DwarningAsError=true"]

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop" @ "master"

section Caching

lean_lib Caching where
  roots := #[`Caching]

lean_exe «get-cache» where
  root := `Caching.GetCache

lean_exe «put-cache» where
  root := `Caching.PutCache

end Caching
