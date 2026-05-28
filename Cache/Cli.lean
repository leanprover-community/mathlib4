/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# Cache CLI option parsing

Pure helpers for the cache binary's option parsing — extracted from `Cache.Main`
so they can be unit-tested without importing `Cache.Main` (which defines a
top-level `main` that would collide with the test binary's entrypoint).

The cache binary partitions its arguments into named options (`--name=value`)
and positional arguments before dispatch. Boolean flags (`--name`) are listed
separately. These helpers implement the partitioning and validation rules.
-/

namespace Cache.Cli

/-- The named options supported by the CLI. -/
def knownNamedOpts : List String := ["repo", "staging-dir", "cache-from", "container", "scope"]

/-- The flag options supported by the CLI. -/
def knownFlagOpts : List String := ["help"]

/-- Parses an optional `--foo=bar` option. Returns the value for the
last-mentioned occurrence (so a later `--foo=` overrides an earlier one). -/
def parseNamedOpt (opt : String) (args : List String) : IO (Option String) := do
  let pref := s!"--{opt}="
  if let some a := args.findRev? (fun a => a.startsWith pref) then
    let val := a.drop pref.length
    return some val.toString
  return none

/-- Parses a boolean `--foo` flag. True iff the bare token `--foo` appears
anywhere in `args`. -/
def parseFlagOpt (opt : String) (args : List String) : Bool :=
  args.elem s!"--{opt}"

/-- Check whether `opt` (e.g. `"--repo=foo"` or `"--help"`) is a recognized
option. Used to error out on unknown `--`-prefixed tokens so typos like
`--scoop=` don't get silently ignored. -/
def isKnownOpt (opt : String) : Bool :=
  knownNamedOpts.any (opt.startsWith s!"--{·}=") ||
  knownFlagOpts.any (opt == s!"--{·}")

end Cache.Cli
