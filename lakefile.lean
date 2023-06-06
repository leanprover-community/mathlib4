import Lake

open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
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
require llm from git "https://github.com/leanprover-community/llm" @ "main"
require lean_pinecone from git "https://github.com/adamtopaz/lean_pinecone" @ "master"
require lean_embedding from git "https://github.com/adamtopaz/lean_embedding" @ "master"

lean_lib Cache where
  moreLeanArgs := moreLeanArgs
  roots := #[`Cache]

lean_exe cache where
  root := `Cache.Main

lean_lib MathlibExtras where
  roots := #[`MathlibExtras]

lean_exe embed where
  supportInterpreter := true
  root := `Embed.Main
