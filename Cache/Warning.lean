/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Query

/-!
# Read-time advisories

Two stderr-only notices `cache get` prints before reading:

* a security warning when the read is taken off the repo's default trust
  boundary (a scope, a widened `--cache-from`, or a `--repo` that diverges
  from the git remote), and
* a hint pointing an uncached fork HEAD at `cache query` and the SHA-scoped
  workflow.
-/

namespace Cache.Requests

/--
`true` iff the resolved scope (see `getRepoScope`) equals the checked-out HEAD.

A HEAD scope only serves artifacts built from the commit already checked out,
and it is what an unscoped `cache get` reads anyway — the forks round defaults
to the HEAD namespace (see `expandDownloadRounds`). So an explicit HEAD scope
(e.g. CI's `MATHLIB_CACHE_REPO_SCOPE`, set to the build SHA on every fork
build) just pins the default behavior and warrants no warning.

`false` when no scope is set or HEAD cannot be determined.
-/
def scopeIsHead : IO Bool := do
  let some scope ← getRepoScope | return false
  let head ← try getGitCommitHash catch _ => return false
  return head == scope

/--
Condition to determine if a non-default scope warning should be printed.

Returns `true` if any of these hold:
0. `--unsafe` was passed (`unsafeWindow?` is `some _`): the read walks several
   fork commits and trusts whoever built each of them
1. `MATHLIB_CACHE_REPO_SCOPE` is set in the environment (any non-empty value)
   and differs from the checked-out HEAD (see `scopeIsHead`)
2. `--cache-from` was passed and widens the lookup chain beyond `defaultContainersForRepo` for the resolved repo
3. `--repo` was passed and does not match the git remote (`detectedRepo?`)

`detectedRepo?` is the repo reported by the git remote (from `resolveRepo`,
probed once per command); it is `none` if it could not be determined.

Otherwise returns `false` (default lookup chain, no warning needed).
-/
def shouldWarnNonDefaultScope (repoExplicit? detectedRepo? : Option String)
    (cliCacheFromOverride? : Option (List Container)) (resolvedRepo : String)
    (unsafeWindow? : Option Nat := none) :
    IO Bool := do
  -- Condition 0: `--unsafe` (with its SHA window) — the most permissive read.
  if unsafeWindow?.isSome then return true

  -- Condition 1: `--scope=` flag or `MATHLIB_CACHE_REPO_SCOPE` env var supplied.
  -- A HEAD scope is exempt: trust-equivalent to no scope (see `scopeIsHead`).
  if (← getRepoScope).isSome then
    unless (← scopeIsHead) do return true

  -- Condition 2: --cache-from CLI override widens the lookup chain
  match cliCacheFromOverride? with
  | some cliOverride =>
    let defaultContainers := defaultContainersForRepo resolvedRepo
    unless cliOverride == defaultContainers do
      return true
  | none => pure ()

  -- Condition 3: --repo was explicitly passed AND does not match the git remote.
  -- Only fires when the user explicitly overrode --repo; defaulting to MATHLIBREPO
  -- from a fork checkout is normal and does not warn.
  match repoExplicit?, detectedRepo? with
  | some explicitRepo, some detected =>
    unless explicitRepo == detected do
      return true
  -- No --repo override, or the remote couldn't be determined: don't warn.
  | _, _ => pure ()

  return false

/--
Print a prominent security warning to stderr when reading at a non-default scope.

The warning includes:
- A clear statement that the user is trusting artifacts at a non-default scope
- The scope details (container, repo, SHA as applicable)
- Why the warning is being issued (which condition triggered it)
-/
def printNonDefaultScopeWarning (repo : String) (triggerReason : String) : IO Unit := do
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
Determine the reason why a non-default scope warning is being issued.

Returns a human-readable string describing which condition triggered the warning.
-/
def getNonDefaultScopeReason (repoExplicit? detectedRepo? : Option String)
    (cliCacheFromOverride? : Option (List Container)) (resolvedRepo : String)
    (unsafeWindow? : Option Nat := none) :
    IO String := do
  -- Check conditions in order; return the first that matches.

  -- Condition 0: `--unsafe` walks up to `window` fork commits, trusting each.
  if let some window := unsafeWindow? then
    return s!"--unsafe (automatic walk over up to {window} fork commit(s); \
      trusting whoever built them)"

  -- Condition 1: `--scope=` flag (preferred form) or `MATHLIB_CACHE_REPO_SCOPE`
  -- env var (CI form). Reported with the source that set it. A HEAD scope is
  -- exempt, mirroring `shouldWarnNonDefaultScope`.
  unless (← scopeIsHead) do
    if let some s ← scopeOverride.get then
      return s!"--scope={s} (explicit per-commit scope)"
    let scope? ← IO.getEnv "MATHLIB_CACHE_REPO_SCOPE"
    if let some scope := scope? then
      let trimmed := scope.trimAscii
      if !trimmed.isEmpty then
        return s!"MATHLIB_CACHE_REPO_SCOPE={trimmed} (explicit per-commit scope)"

  -- Condition 2: --cache-from override
  if let some cliOverride := cliCacheFromOverride? then
    let defaultContainers := defaultContainersForRepo resolvedRepo
    if cliOverride != defaultContainers then
      let overrideStr := ", ".intercalate (cliOverride.map Container.name)
      return s!"--cache-from={overrideStr} (explicit container override)"

  -- Condition 3: --repo was explicitly passed AND doesn't match the git remote
  match repoExplicit?, detectedRepo? with
  | some explicitRepo, some detected =>
    if explicitRepo != detected then
      return s!"--repo={explicitRepo} (overrides detected git remote: {detected})"
  | _, _ => pure ()

  return "unknown reason"

/--
Print the non-default-scope warning if any of the three conditions hold.

Called before a read (`cache get`). The warning is informational only — it
never prompts, so it stays safe to run in CI.
-/
def warnIfNonDefaultScope (repoExplicit? detectedRepo? : Option String)
    (cliCacheFromOverride? : Option (List Container)) (resolvedRepo : String)
    (unsafeWindow? : Option Nat := none) :
    IO Unit := do
  if (← shouldWarnNonDefaultScope repoExplicit? detectedRepo? cliCacheFromOverride? resolvedRepo
        unsafeWindow?)
    then
    let reason ← getNonDefaultScopeReason repoExplicit? detectedRepo? cliCacheFromOverride?
      resolvedRepo unsafeWindow?
    printNonDefaultScopeWarning resolvedRepo reason

/--
If the user is on a commit that hasn't been cached for this fork (no marker
present at `forks/m/{repo}/{HEAD-sha}`), print an informational note
explaining the new SHA-scoped behavior and pointing at `cache query`.

Fires only on naive `cache get` invocations:
- no `--scope=` / `MATHLIB_CACHE_REPO_SCOPE` set (else the user has already
  picked a scope and the non-default-scope warning is doing the talking)
- no `--cache-from` override (else they've already taken explicit
  responsibility for the lookup chain)
- the resolved repo's default lookup chain reads from `forks` (otherwise SHA
  scoping is not relevant)
- HEAD is not already an ancestor of `master`. From a personal-fork checkout
  sitting on `master` (or an undiverged branch), the fork's SHA-scoped marker is
  structurally absent, but `master` is first in the fork lookup chain and serves
  every file by hash — there is nothing fork-specific to build, so the note would
  be a pure false positive.

One HEAD probe per invocation; the message is stderr-only so it doesn't
mix with `cache get`'s stdout output.

`repo` is the already-resolved repo (see `resolveRepo`).
-/
def informIfHeadNotBuilt (repo : String) : IO Unit := do
  if (← getRepoScope).isSome then return
  if (← cacheFromOverride.get).isSome then return
  unless (defaultContainersForRepo repo).contains Container.forks do return
  -- HEAD already on (an ancestor of) master: master CI builds these commits and
  -- the master container (first in the fork lookup chain) serves their artifacts
  -- by hash, so there is nothing fork-specific to build. The forks marker is
  -- structurally absent here, which would otherwise trigger a misleading note.
  if (← headIsAncestorOfMaster) then return
  let sha ← try getGitCommitHash catch _ => return
  let hasMarker ← probeContainerForSHA Container.forks repo sha
  if hasMarker then return
  let lines : List String := [
    "",
    s!"NOTE: no cache found for HEAD ({sha}) on fork {repo}.",
    "This commit hasn't been built by CI for this fork yet. You'll still",
    "get cache hits for files that match mathlib's master cache; only",
    "files unique to this PR will need to be rebuilt.",
    "",
    "To use a prior CI run from this fork, find a cached commit:",
    "    lake exe cache query",
    "",
    "then re-run with:",
    "    lake exe cache get --scope=<that-sha>",
    "",
    "Important: using another commit's scope means trusting the artifacts",
    "produced at that commit. `cache get` will print a security notice",
    "when you do.",
    "",
  ]
  for line in lines do
    IO.eprintln line

end Cache.Requests
