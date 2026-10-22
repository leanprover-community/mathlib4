/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Workflow.Defs

/-!
# The container-chain read

The read mechanism of the developer workflow: a trust-ordered chain of
containers, each read under the base the workflow gives it, with the
per-commit scope on the rounds of the containers that have per-commit
namespaces (`Container.perCommit`). The workflow supplies its default chain
(`Cache.Workflow.Developer.containers`); the chain options (`ChainOptions`,
from `--cache-from` and `MATHLIB_CACHE_FROM`) replace it. The public-cache
workflow has no chain; it reads one location
(`Cache.Workflow.Public.location`).
-/

public section

namespace Cache.Workflow

open Cache.Requests
open System (FilePath)

/-- The chain options of a chain read. `--cache-from` (`cli?`) wins over
`MATHLIB_CACHE_FROM` (`env?`), the chain CI sets per job to match its write
target; only `cli?` counts as the user's choice for the security notice. -/
structure ChainOptions where
  cli? : Option (List Container) := none
  env? : Option (List Container) := none
  deriving Repr, BEq, Inhabited

namespace ChainOptions

/-- `--cache-from=LIST`: the chain of a read. The parser validates the
container names (`Cli.ParseableType (List Container)`). -/
def flag : Cli.Flag := {
  longName := "cache-from"
  description := s!"A trust-ordered, comma-separated list of the containers to read, e.g. \
    master,forks, one of {", ".intercalate (Container.all.map Container.name)}. Replaces the \
    workflow's chain; on the canonical repo it selects the developer-cache workflow."
  type := List Container }

/-- The chain that replaces the workflow's, if any. -/
def chain? (o : ChainOptions) : Option (List Container) := o.cli? <|> o.env?

/--
The chain options of the parsed command line `p` and the settings `s`:
`--cache-from=LIST` (`flag`) and `MATHLIB_CACHE_FROM`. An unknown container
name in the variable is ignored with a warning, so a stale CI setting degrades
to the workflow's chain.
-/
def parse (p : Cli.Parsed) (s : Settings) : IO ChainOptions := do
  let cli? := (p.flag? flag.longName).map (·.as! (List Container))
  let env? ← match s.cacheFrom? with
    | none => pure none
    | some s => match parseCacheFromList s with
      | some cs => pure (some cs)
      | none =>
        IO.eprintln s!"Warning: ignoring MATHLIB_CACHE_FROM={s} \
          (unrecognized container name). Known containers: \
          {", ".intercalate (Container.all.map Container.name)}."
        pure none
  return { cli?, env? }

end ChainOptions

namespace Chain

/-- The chain a read tries: the chain options' chain, else the workflow's
`default`. -/
def resolve (default : List Container) (options : ChainOptions) : List Container :=
  options.chain?.getD default

/-- Pair each container in a chain with its read base, which the workflow
decides (`readBase`). The result keeps the chain's trust order. -/
def withBases (chain : List Container) (readBase : Container → String) :
    List (Container × String) :=
  chain.map fun c => (c, readBase c)

/--
Expand a chain, paired with read bases, into the locations to read for
`repo`, one download round each.

A scope applies to the containers with per-commit namespaces
(`Container.perCommit`, that is `forks`) and to no other. Without `--unsafe`
(`unsafeScopes` empty) such a round reads at the explicit `sha?`, else at
`headScope?`, the checked-out HEAD resolved by the caller: fork uploads live
under the per-commit namespace, so a plain `cache get` reads what CI built for
the commit the reader has checked out. With `--unsafe` (`unsafeScopes`
non-empty) the container expands into one round per discovered SHA, most
recent first, and `sha?` is dropped; the walk probed the markers of those SHAs.
Every other container reads unscoped.
-/
def locations (chain : List (Container × String)) (repo : String) (sha? : Option String)
    (unsafeScopes : List String) (headScope? : Option String := none) :
    List Location :=
  chain.flatMap fun (c, base) =>
    if c.perCommit then
      if unsafeScopes.isEmpty then [c.location base repo (sha? <|> headScope?)]
      else unsafeScopes.map fun sha => c.location base repo (some sha)
    else [c.location base repo none]

/--
The locations of a chain read for `repo`: the chain (`resolve default
options`) paired with its read bases and expanded into rounds (`locations`),
with `scope?` and, absent one, the HEAD of the Mathlib checkout for the
per-commit rounds. `unsafeScopes` is the `--unsafe` walk's result, empty
otherwise.
-/
def readLocations (default : List Container) (readBase : Container → String)
    (options : ChainOptions) (scope? : Option Scope) (repo : String)
    (unsafeScopes : List String := []) : IO.CacheM (List Location) := do
  let chain := withBases (resolve default options) readBase
  -- With no explicit scope, the per-commit round defaults to HEAD. This adds
  -- no trust over an unscoped forks read: the namespace can only hold
  -- artifacts built from the commit the reader already has.
  let headScope? ← if scope?.isNone && unsafeScopes.isEmpty then
      try pure (some (← getGitCommitHash)) catch _ => pure none
    else pure none
  return locations chain repo (scope?.map (·.sha)) unsafeScopes headScope?

end Chain

end Cache.Workflow
