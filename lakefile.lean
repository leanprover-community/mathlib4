import Lake

open Lake DSL

package mathlib

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := #[
    "-DwarningAsError=true",
    "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
  ]

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop" @ "master"

require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4" @ "v0.0.10"

lean_lib Cache where
  roots := #[`Cache]

lean_exe cache where
  root := `Cache.Main
