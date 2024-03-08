import Lake

open Lake DSL

package mathlib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  -- These are additional settings which do not affect the lake hash,
  -- so they can be enabled in CI and disabled locally or vice versa.
  -- Warning: Do not put any options here that actually change the olean files,
  -- or inconsistent behavior may result
  weakLeanArgs :=
    if get_config? CI |>.isSome then
      #["-DwarningAsError=true"]
    else
      #[]

/-!
## Mathlib dependencies on upstream projects.
-/

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/leanprover-community/quote4" @ "master"
require aesop from git "https://github.com/leanprover-community/aesop" @ "master"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.30"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"
require importGraph from git "https://github.com/leanprover-community/import-graph.git" @ "main"

/-!
## Mathlib libraries
-/

@[default_target]
lean_lib Mathlib

lean_lib Cache
lean_lib MathlibExtras
lean_lib Archive
lean_lib Counterexamples
/-- Additional documentation in the form of modules that only contain module docstrings. -/
lean_lib docs where
  roots := #[`docs]

/-!
## Executables provided by Mathlib
-/

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
lean_exe cache where
  root := `Cache.Main

/-- `lake exe checkYaml` verifies that all declarations referred to in `docs/*.yaml` files exist. -/
lean_exe checkYaml where
  srcDir := "scripts"
  supportInterpreter := true

/-- `lake exe shake` checks files for unnecessary imports. -/
lean_exe shake where
  root := `Shake.Main
  supportInterpreter := true

/-!
## Other configuration
-/

/--
When a package depending on Mathlib updates its dependencies,
update its toolchain to match Mathlib's and fetch the new cache.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.name = pkg.name then
    return -- do not run in Mathlib itself
  /-
  Once Lake updates the toolchains,
  this toolchain copy will be unnecessary.
  https://github.com/leanprover/lean4/issues/2752
  -/
  let wsToolchainFile := rootPkg.dir / "lean-toolchain"
  let mathlibToolchain := ← IO.FS.readFile <| pkg.dir / "lean-toolchain"
  IO.FS.writeFile wsToolchainFile mathlibToolchain
  if (← IO.getEnv "MATHLIB_NO_CACHE_ON_UPDATE") != some "1" then
    /-
    Instead of building and running cache via the Lake API,
    spawn a new `lake` since the toolchain may have changed.
    -/
    let exitCode ← IO.Process.spawn {
      cmd := "elan"
      args := #["run", "--install", mathlibToolchain.trim, "lake", "exe", "cache", "get"]
    } >>= (·.wait)
    if exitCode ≠ 0 then
      logError s!"{pkg.name}: failed to fetch cache"
