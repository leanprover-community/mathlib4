import Lake

open Lake DSL


/-!
## Mathlib dependencies on upstream projects
-/

require "leanprover-community" / "batteries" @ git "main"
require "leanprover-community" / "Qq" @ git "master"
require "leanprover-community" / "aesop" @ git "master"
require "leanprover-community" / "proofwidgets" @ git "v0.0.41"
require "leanprover-community" / "importGraph" @ git "main"

/-!
## Options for building mathlib
-/

/-- These options are used
* as `leanOptions`, prefixed by `` `weak``, so that `lake build` uses them;
* as `moreServerArgs`, to set their default value in mathlib
  (as well as `Archive`, `Counterexamples` and `test`).
-/
abbrev mathlibOnlyLinters : Array LeanOption := #[
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.missingEnd, true⟩,
  ⟨`linter.cdot, true⟩,
  ⟨`linter.dollarSyntax, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.longLine, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.style.setOption, true⟩
]

/-- These options are passed as `leanOptions` to building mathlib, as well as the
`Archive` and `Counterexamples`. (`tests` omits the first two options.) -/
abbrev mathlibLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    mathlibOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package mathlib where
  leanOptions := mathlibLeanOptions
  -- Mathlib also enforces these linter options, which are not active by default.
  moreServerOptions := mathlibOnlyLinters
  -- These are additional settings which do not affect the lake hash,
  -- so they can be enabled in CI and disabled locally or vice versa.
  -- Warning: Do not put any options here that actually change the olean files,
  -- or inconsistent behavior may result
  -- weakLeanArgs := #[]

/-!
## Mathlib libraries
-/

@[default_target]
lean_lib Mathlib

-- NB. When adding further libraries, check if they should be excluded from `getLeanLibs` in
-- `scripts/mk_all.lean`.
lean_lib Cache
lean_lib LongestPole

lean_lib Archive where
  leanOptions := mathlibLeanOptions
  moreServerOptions := mathlibOnlyLinters

lean_lib Counterexamples where
  leanOptions := mathlibLeanOptions
  moreServerOptions := mathlibOnlyLinters

/-- Additional documentation in the form of modules that only contain module docstrings. -/
lean_lib docs where
  roots := #[`docs]

/-!
## Executables provided by Mathlib
-/

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
lean_exe cache where
  root := `Cache.Main

/-- `lake exe check-yaml` verifies that all declarations referred to in `docs/*.yaml` files exist. -/
lean_exe «check-yaml» where
  srcDir := "scripts"
  supportInterpreter := true

/-- `lake exe mk_all` constructs the files containing all imports for a project. -/
lean_exe mk_all where
  srcDir := "scripts"
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/-- `lake exe shake` checks files for unnecessary imports. -/
lean_exe shake where
  root := `Shake.Main
  supportInterpreter := true

/-- `lake exe lint-style` runs text-based style linters. -/
lean_exe «lint-style» where
  srcDir := "scripts"

/--
`lake exe pole` queries the Mathlib speedcenter for build times for the current commit,
and then calculates the longest pole
(i.e. the sequence of files you would be waiting for during a infinite parallelism build).
-/
lean_exe pole where
  root := `LongestPole.Main
  supportInterpreter := true
  -- Executables which import `Lake` must set `-lLake`.
  weakLinkArgs := #["-lLake"]

/--
`lake exe test` is a thin wrapper around `lake exe batteries/test`, until
https://github.com/leanprover/lean4/issues/4121 is resolved.

You can also use it as e.g. `lake exe test conv eval_elab` to only run the named tests.
-/
@[test_driver]
lean_exe test where
  -- We could add the above `leanOptions` and `moreServerOptions`: currently, these do not take
  -- effect as `test` is a `lean_exe`. With a `lean_lib`, it would work...
  srcDir := "scripts"

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
