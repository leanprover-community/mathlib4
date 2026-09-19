/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Cli
import Cache.Repo

/-!
# The per-commit scope

The scope a fork read or write addresses: the SHA whose per-commit namespace
in the `forks` container the round reads or the upload fills. It comes from
`--scope=REF` (`Scope.flag`) or `MATHLIB_CACHE_REPO_SCOPE` (`Scope.parse`).
The developer-cache and nightly workflows read at it; the developer-cache
upload writes under it (`Upload`); the flat upload has no per-commit
namespaces and rejects a set scope.
-/

namespace Cache

open Cache.Requests
open System (FilePath)

/-- Where a per-commit scope came from; the security notice names the source. -/
inductive ScopeSource where
  /-- `--scope=REF`. -/
  | flag
  /-- `MATHLIB_CACHE_REPO_SCOPE`. -/
  | env
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A per-commit scope: the SHA whose namespace a fork read or write addresses. -/
structure Scope where
  sha : String
  source : ScopeSource
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Whether `scope` is a well-formed per-commit scope: a nonempty run of hex
digits, at most 64 of them (a commit SHA, abbreviated or full). The scope
lands in URL paths and in file names — the fork namespace `f/{repo}/{scope}/`,
the marker `m/{repo}/{scope}`, and the marker's local temp file — so anything
else (a path separator, `..`, an unresolved ref name) is a misconfiguration
that must fail loudly rather than leak into a path.
-/
def isValidScope (scope : String) : Bool :=
  !scope.isEmpty && scope.length ≤ 64 &&
    scope.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

namespace Scope

/-- `--scope=REF`: the per-commit namespace of a read or a write. -/
def flag : Cli.Flag := {
  longName := "scope"
  description := "The per-commit namespace, as any git ref `git rev-parse` accepts (HEAD, a \
    branch, a tag, a SHA). A read takes the fork's namespace for that commit instead of the \
    checked-out HEAD; use the SHA `cache query` reports. An upload fills that namespace. \
    Reading another commit's scope trusts the artifacts built at that commit, and get prints \
    a security notice."
  type := String }

/-- A scope from `sha`; throws when `sha` is not a hex SHA (`isValidScope`). -/
def ofString (sha : String) (source : ScopeSource) : IO Scope := do
  unless isValidScope sha do
    throw <| IO.userError s!"invalid cache scope '{sha}': a scope is a commit SHA (hex \
      digits; --scope also accepts any ref `git rev-parse` can resolve from inside a git checkout)"
  return { sha, source }

/-- The environment's scope, `MATHLIB_CACHE_REPO_SCOPE`, if set. An empty value
means unset (`nonEmptyEnvValue`). -/
def ofEnv : IO (Option Scope) := do
  match (← getEnvNonEmpty "MATHLIB_CACHE_REPO_SCOPE") with
  | some sha => some <$> ofString sha .env
  | none => pure none

/--
The scope of the parsed command line `p`: `--scope=REF` (`flag`), else
`MATHLIB_CACHE_REPO_SCOPE`, else none. `--scope` accepts any git ref
`git rev-parse` resolves in `cwd` (HEAD, branch, tag, SHA) and falls through
to the literal value when git cannot (a bare SHA outside a git checkout).
-/
def parse (p : Cli.Parsed) (cwd : FilePath := ".") : IO (Option Scope) := do
  match p.flag? flag.longName with
  | some f =>
    let ref := f.as! String
    let sha ← try resolveGitRef ref cwd catch _ => pure ref
    some <$> ofString sha .flag
  | none => ofEnv

end Scope

end Cache
