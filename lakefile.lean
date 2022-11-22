import Lake

open Lake DSL

package mathlib

@[defaultTarget]
lean_lib Mathlib where
  moreLeanArgs := #["-DwarningAsError=true"]

@[defaultTarget]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"

-- Breaks mathport CI due to https://github.com/leanprover/lake/issues/137
-- TODO: reenable once Lake 4.1.0 is out
-- require aesop from git "https://github.com/JLimperg/aesop" @ "master"
