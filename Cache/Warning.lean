/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Query

/-!
# Read-time advisories

Two stderr-only notices around a `cache get` read:

* before reading: a security warning when the read is taken off the repo's
  default trust boundary (a scope, a widened `--cache-from`, or a `--repo`
  that diverges from the git remote), and
* after reading: guidance for files no container served, keyed on the actual
  misses — a naive fork read is pointed at `cache query` and the SHA-scoped
  workflow, every other read gets the generic divergence warning.
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
Lines for the missing-files warning on a fork checkout whose HEAD has no
published fork cache: a previous CI build of this fork may hold the missing
files, so the message points at `cache query` and the SHA-scoped workflow.
Selected by `forkHintSHA?`.
-/
def missingFilesForkLines (repo sha : String) (missing : Nat) : List String := [
  "",
  s!"NOTE: {missing} file(s) were not found in any cache for fork {repo}.",
  s!"CI has not published a fork cache for HEAD ({sha}) — most likely it",
  "hasn't built this commit yet. The missing files will be built locally",
  "by `lake build`.",
  "",
  "To reuse a previous CI build from this fork instead, find a cached commit:",
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

/--
Lines for the missing-files warning when the fork-workflow hint does not
apply (see `forkHintSHA?`): the generic divergence explanation.
-/
def missingFilesGenericLines (missing : Nat) : List String := [
  s!"Warning: {missing} file(s) were not found in the cache.",
  "This usually means that your local checkout of mathlib4 has diverged from upstream.",
  "",
  "  * If you push your commits to a PR to the mathlib4 repository",
  "    (use a draft PR if it is not ready for review),",
  "    then CI will build the oleans and they will be available later.",
  "  * If you have already opened a PR, this may mean",
  "    the CI build has failed part-way through building.",
]

/--
When the missing-files warning should point at the fork workflow (`cache
query` / `--scope`), return the HEAD SHA it should mention; `none` means the
generic divergence warning applies.

The fork hint fires only for a naive `cache get` on a fork checkout whose
HEAD has no published fork cache:
- not in `--unsafe` mode (that read already walked fork scopes and reported
  what they served)
- no `--scope=` / `MATHLIB_CACHE_REPO_SCOPE` set (the user has already picked
  a scope and the non-default-scope warning did the talking)
- no `--cache-from` override (the user has taken explicit responsibility for
  the lookup chain)
- the repo is a fork, not a first-party repo: the canonical repos don't build
  into the per-commit `forks` namespace this hint points at
- HEAD is not an ancestor of `master`: misses there are master-container lag
  (CI still building master), which no fork scope can serve
- the fork marker for HEAD is absent; when it is present the HEAD scope was
  already read and came up short anyway, so pointing back at it would not help

Guards are ordered cheapest first; the marker probe (one HTTPS round-trip)
runs only when every local check passes.

`repo` is the already-resolved repo (see `resolveRepo`).
-/
def forkHintSHA? (repo : String) (unsafeMode : Bool) : IO (Option String) := do
  if unsafeMode then return none
  if (← getRepoScope).isSome then return none
  if (← cacheFromOverride.get).isSome then return none
  if isCanonicalRepo repo then return none
  if (← headIsAncestorOfMaster) then return none
  let sha ← try getGitCommitHash catch _ => return none
  if (← probeContainerForSHA Container.forks repo sha) then return none
  return some sha

/--
Print guidance for files that no download round served, to stderr.

Keyed on the download's actual outcome rather than an upfront proxy: with
`missing = 0` nothing is printed. In particular, a fork PR that changes no
Lean module gets every file from mathlib's master cache and produces no note,
even though no fork cache exists for its commits — its absence has no
consequence. When files are missing, reads that `forkHintSHA?` accepts get
the fork-workflow hint; every other read gets the generic divergence warning.
-/
def warnIfMissingFiles (repo : String) (missing : Nat) (unsafeMode : Bool := false) :
    IO Unit := do
  if missing == 0 then return
  let lines ← match ← forkHintSHA? repo unsafeMode with
    | some sha => pure (missingFilesForkLines repo sha missing)
    | none => pure (missingFilesGenericLines missing)
  for line in lines do
    IO.eprintln line

end Cache.Requests
