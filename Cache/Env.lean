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

end Cache
