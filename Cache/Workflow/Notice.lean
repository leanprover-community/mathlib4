/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Workflow.Chain

/-!
# The non-default-scope notice

The stderr-only security warning a chain read (the developer and nightly
workflows) prints before reading when the read is taken off the workflow's
default trust boundary: a scope other than HEAD, a `--cache-from` that differs
from the workflow's chain, a `--repo` that diverges from the git remote, or
`--unsafe`.
-/

namespace Cache.Workflow.Notice

open Cache.Requests
open System (FilePath)

/-- What a chain read tells the notice about itself. -/
structure Read where
  /-- The `--repo=` value, if given. -/
  repoExplicit? : Option String := none
  /-- The repo the git remote reports, if any. -/
  detectedRepo? : Option String := none
  /-- The chain options of the read. -/
  chain : ChainOptions := {}
  /-- The workflow's own chain. -/
  defaultChain : List Container
  /-- The scope of the read, if any. -/
  scope? : Option Scope := none
  /-- The `--unsafe` window, if set. -/
  unsafeWindow? : Option Nat := none
  /-- The mathlib checkout whose HEAD a scope is compared with. -/
  cwd : FilePath := "."

/--
`true` iff `scope` equals the checked-out HEAD of `cwd`.

A HEAD scope only serves artifacts built from the commit already checked out,
and an unscoped chain read reads it anyway: the forks round defaults to the
HEAD namespace (see `Cache.Workflow.Chain.rounds`). An explicit HEAD scope
(CI's `MATHLIB_CACHE_REPO_SCOPE`, set to the build SHA on every fork build)
pins the default behavior and warrants no warning.

`false` when HEAD cannot be determined.
-/
def scopeIsHead (scope : Scope) (cwd : FilePath := ".") : IO Bool := do
  let head ← try getGitCommitHash cwd catch _ => return false
  return head == scope.sha

/--
Whether the notice applies. `true` if any of these hold:
0. `--unsafe` was passed (`unsafeWindow?`): the read walks several fork
   commits and trusts whoever built each of them
1. a scope is set (`scope?`) and differs from the checked-out HEAD of `cwd`
   (see `scopeIsHead`)
2. `--cache-from` was passed (`chain.cli?`) and differs from `defaultChain`,
   the workflow's own chain
3. `--repo` was passed (`repoExplicit?`) and does not match the git remote
   (`detectedRepo?`), or names a non-canonical repo with no detectable remote
   to compare against

`detectedRepo?` is the repo reported by the git remote (from `resolveRepo`,
probed once per command); it is `none` if it could not be determined.
-/
def applies (r : Read) : IO Bool := do
  -- Condition 0: `--unsafe` (with its SHA window) — the most permissive read.
  if r.unsafeWindow?.isSome then return true

  -- Condition 1: a scope other than HEAD. A HEAD scope is exempt:
  -- trust-equivalent to no scope (see `scopeIsHead`).
  if let some scope := r.scope? then
    unless (← scopeIsHead scope r.cwd) do return true

  -- Condition 2: --cache-from differs from the workflow's chain.
  if let some cliChain := r.chain.cli? then
    unless cliChain == r.defaultChain do return true

  -- Condition 3: --repo was explicitly passed AND does not match the git remote.
  -- Only fires when the user explicitly overrode --repo; defaulting to MATHLIBREPO
  -- from a fork checkout is normal and does not warn.
  match r.repoExplicit?, r.detectedRepo? with
  | some explicitRepo, some detected =>
    unless explicitRepo == detected do return true
  | some explicitRepo, none =>
    -- No remote to compare against (a dependency fetched as an archive, or a
    -- git failure). A non-canonical --repo then reads that fork's container on
    -- nothing but the flag, so the choice still warrants the notice.
    unless isCanonicalRepo explicitRepo do return true
  | none, _ => pure ()

  return false

/--
The `Reason:` line of the notice: the first condition of `applies` that holds,
in the same order, named so the user can match it to their command line.
-/
def reason (r : Read) : IO String := do
  if let some window := r.unsafeWindow? then
    return s!"--unsafe (automatic walk over up to {window} fork commit(s); \
      trusting whoever built them)"

  if let some scope := r.scope? then
    unless (← scopeIsHead scope r.cwd) do
      match scope.source with
      | .flag => return s!"--scope={scope.sha} (explicit per-commit scope)"
      | .env => return s!"MATHLIB_CACHE_REPO_SCOPE={scope.sha} (explicit per-commit scope)"

  if let some cliChain := r.chain.cli? then
    if cliChain != r.defaultChain then
      let chainStr := ", ".intercalate (cliChain.map Container.name)
      return s!"--cache-from={chainStr} (explicit container override)"

  match r.repoExplicit?, r.detectedRepo? with
  | some explicitRepo, some detected =>
    if explicitRepo != detected then
      return s!"--repo={explicitRepo} (overrides detected git remote: {detected})"
  | some explicitRepo, none =>
    if !isCanonicalRepo explicitRepo then
      return s!"--repo={explicitRepo} (no git remote to compare against; \
        reads that fork's cache)"
  | none, _ => pure ()

  return "unknown reason"

/-- Print the notice to stderr: what the user is trusting, for which
repository, and the reason. -/
def printWarning (repo : String) (triggerReason : String) : IO Unit := do
  let lines : List String := [
    "=================================================================",
    "SECURITY: reading cache at a non-default scope",
    "=================================================================",
    "You are reading cache artifacts at a scope outside the default trust",
    "boundary for this repo. The cache cannot verify the contents of these",
    "artifacts; you are choosing to trust whoever uploaded them.",
    "",
    s!"Repository: {repo}",
    s!"Reason: {triggerReason}",
    "=================================================================",
  ]
  for line in lines do
    IO.eprintln line

/--
Print the notice when it applies, before a chain read for `repo`. The notice
is informational: it prints and returns, so CI runs are unaffected.
-/
def emit (r : Read) (repo : String) : IO Unit := do
  if (← applies r) then
    printWarning repo (← reason r)

end Cache.Workflow.Notice
