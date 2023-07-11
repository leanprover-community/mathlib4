import Lake

open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := #[
  "-DwarningAsError=true"
] ++ moreServerArgs

package mathlib where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := moreLeanArgs

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop" @ "master"
require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "nightly"
require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4" @ "v0.0.11"

lean_lib Cache where
  moreLeanArgs := moreLeanArgs
  roots := #[`Cache]

lean_exe cache where
  root := `Cache.Main

lean_lib MathlibExtras where
  roots := #[`MathlibExtras]

lean_lib Archive where
  roots := #[`Archive]

lean_lib Counterexamples where
  roots := #[`Counterexamples]

lean_lib ImportGraph where
  roots := #[`ImportGraph]

lean_exe graph where
  root := `ImportGraph.Main
