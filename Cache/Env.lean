/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# Cache environment variable parsing

Helpers for reading the cache tool's environment variables: an empty or
whitespace-only value means unset, a base URL also loses its trailing slashes,
and a boolean flag accepts `1`/`true` and `0`/`false`.

`Settings` holds the variables that decide what a command does, read once per
command (`Settings.read`).
-/

namespace Cache

/--
Trimmed value of an environment variable. An empty or whitespace-only value
means unset.

CI wires the cache variables from a GitHub Actions `vars` lookup. That lookup
yields an empty string for an undefined variable, and such a value selects the
same behavior as an absent one.
-/
def nonEmptyEnvValue (value? : Option String) : Option String :=
  (value?.map (·.trimAscii.copy)).filter (!·.isEmpty)

/-- Reads `name` from the environment through `nonEmptyEnvValue`. -/
def getEnvNonEmpty (name : String) : IO (Option String) := do
  return nonEmptyEnvValue (← IO.getEnv name)

/--
Value of an environment variable that names a base URL. The same empty rule as
`nonEmptyEnvValue` applies, and the base also loses its trailing slashes, so a
later `/{path}` follows a single separator.
-/
def normalizeBaseURL (value? : Option String) : Option String :=
  (value?.map fun v => (v.trimAscii.dropEndWhile '/').copy).filter (!·.isEmpty)

/--
Value of the boolean environment variable `name`, given its raw value `value?`:
`1` and `true` are on, `0` and `false` are off, and case does not matter. An
absent, empty, or whitespace-only value takes `ifUnset`; any other value warns
on stderr and takes `ifUnset` as well.
-/
def parseEnvFlag (name : String) (value? : Option String) (ifUnset : Bool) : IO Bool := do
  let some value := nonEmptyEnvValue value? | return ifUnset
  match value.toLower with
  | "1" | "true" => return true
  | "0" | "false" => return false
  | _ =>
    IO.eprintln s!"Warning: ignoring {name}={value} (expected 1, true, 0 or false)."
    return ifUnset

/-- Value of the boolean environment variable `name`, read from the environment
and parsed by `parseEnvFlag`. -/
def getEnvFlag (name : String) (ifUnset : Bool) : IO Bool := do
  parseEnvFlag name (← IO.getEnv name) ifUnset

/-- The environment variables that decide what a command does. -/
structure Settings where
  /-- `MATHLIB_CACHE_GET_URL`: a flat endpoint that serves every file at
  `{url}/f/{hash}.ltar`, for third parties who serve their own cache. -/
  getURL? : Option String := none
  /-- `MATHLIB_CACHE_BASE_URL`: the host of every container read. -/
  baseURL? : Option String := none
  /-- `MATHLIB_CACHE_DEBUG_USE_LEGACY`: read every container from the Azure
  storage account. -/
  useLegacy : Bool := false
  /-- `MATHLIB_CACHE_FROM`: the chain of a chain read, unparsed. -/
  cacheFrom? : Option String := none
  /-- `MATHLIB_CACHE_REPO_SCOPE`: the per-commit scope, unvalidated. -/
  repoScope? : Option String := none
  /-- `MATHLIB_CACHE_PUT_URL`: the root of an upload. -/
  putURL? : Option String := none
  deriving Repr, BEq, Inhabited

/-- The settings of the process environment. -/
def Settings.read : IO Settings := do
  return {
    getURL? := normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_GET_URL")
    baseURL? := normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_BASE_URL")
    useLegacy := ← getEnvFlag "MATHLIB_CACHE_DEBUG_USE_LEGACY" (ifUnset := false)
    cacheFrom? := ← getEnvNonEmpty "MATHLIB_CACHE_FROM"
    repoScope? := ← getEnvNonEmpty "MATHLIB_CACHE_REPO_SCOPE"
    putURL? := normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_PUT_URL") }

end Cache
