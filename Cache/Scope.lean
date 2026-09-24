/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# The per-commit scope

The scope a fork read or write addresses: the SHA whose per-commit namespace
in the `forks` container the round reads or the upload fills. The developer
and nightly workflows read at it. An upload to `forks` writes under it, and an
upload to another container rejects it (`stagedUploadDestFrom`). The command
line reads it from `--scope=REF` or `MATHLIB_CACHE_REPO_SCOPE`
(`Scope.flag`, `Scope.parse` in `Cache.Cli`).
-/

namespace Cache

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

/-- A scope from `sha`; throws when `sha` is not a hex SHA (`isValidScope`). -/
def Scope.ofString (sha : String) (source : ScopeSource) : IO Scope := do
  unless isValidScope sha do
    throw <| IO.userError s!"invalid cache scope '{sha}': a scope is a commit SHA (hex \
      digits; --scope also accepts any ref `git rev-parse` can resolve from inside a git checkout)"
  return { sha, source }

end Cache
