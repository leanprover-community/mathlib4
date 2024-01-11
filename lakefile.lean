import Lake

open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-Dpp.proofs.withType=false",
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

-- These are additional settings which do not affect the lake hash,
-- so they can be enabled in CI and disabled locally or vice versa.
-- Warning: Do not put any options here that actually change the olean files,
-- or inconsistent behavior may result
def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

package mathlib where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs

/-- `lake exe runMathlibLinter` runs the linter on all of Mathlib (or individual files). -/
-- Due to a change in Lake at v4.1.0-rc1, we need to give this a different name
-- than the `lean_exe runLinter` inherited from Std, or we always run that.
-- See https://github.com/leanprover/lean4/issues/2548
lean_exe runMathlibLinter where
  root := `scripts.runMathlibLinter
  supportInterpreter := true

/-- `lake exe checkYaml` verifies that all declarations referred to in `docs/*.yaml` files exist. -/
lean_exe checkYaml where
  root := `scripts.checkYaml
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/leanprover-community/quote4" @ "master"
require aesop from git "https://github.com/leanprover-community/aesop" @ "master"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.21"

lean_lib Cache where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Cache]

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
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

/-- `lake exe graph` constructs import graphs in `.dot` or graphical formats. -/
lean_exe graph where
  root := `ImportGraph.Main
  supportInterpreter := true

/-- Additional documentation in the form of modules that only contain module docstrings. -/
lean_lib docs where
  roots := #[`docs]
