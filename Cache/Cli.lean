/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# Cache CLI option parsing

Pure helpers for the cache binary's option parsing. They live here rather than
in `Cache.Main` so the test binary can import them directly — `Cache.Main`'s
top-level `main` would otherwise collide with the test entrypoint.

The cache binary partitions its arguments into named options (`--name=value`),
boolean flags (`--name`), and positional arguments before dispatch. These
helpers implement that partitioning and the validation of known option names.
-/

namespace Cache.Cli

/-- The named options supported by the CLI. -/
def knownNamedOpts : List String :=
  ["repo", "staging-dir", "cache-from", "container", "scope", "unsafe-window"]

/-- The flag options supported by the CLI. -/
def knownFlagOpts : List String := ["help", "unsafe"]

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
