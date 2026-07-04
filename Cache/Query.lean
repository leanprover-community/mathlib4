/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# The `cache query` subcommand

Discovers the most recent commit on the current branch that has a cached CI
build, by walking git history back to the merge base with `master` and probing
each commit's per-SHA marker. Diagnostic only: it prints a SHA for the user to
pass to `cache get --scope=`, and never reads or writes artifacts itself.
-/

namespace Cache.Requests

open System (FilePath)

/--
Walk git log backwards from HEAD, starting from `startRef`, stopping at
`stopRef` or after `cap` commits (whichever comes first).

Returns the list of commit SHAs in reverse chronological order (most recent first).
-/
def gitLogWalk (startRef stopRef : String) (cap : Nat) (cwd : FilePath := ".") :
    IO (List String) := do
  -- Construct git log command: walk from startRef to stopRef (if provided) using first-parent.
  -- First-parent follows the main branch across merges, which is the intended behavior.
  let args := if stopRef.isEmpty then
    #["log", startRef, "--first-parent", "--pretty=format:%H", s!"--max-count={cap}"]
  else
    #["log", s!"{startRef}...{stopRef}", "--first-parent", "--pretty=format:%H", s!"--max-count={cap}"]
  let out ← IO.Process.output {cmd := "git", args := args, cwd := cwd}
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"git log failed (exit code {out.exitCode}):\n{out.stderr.trimAscii}"
  let shas := out.stdout.trimAscii.toString.splitOn "\n" |>.filter (· ≠ "")
  pure shas

/--
Determine the merge base between `HEAD` and a target ref (typically `master`).
Falls back to a cap-only walk if the ref is not reachable.
-/
def gitMergeBase (targetRef : String) (cwd : FilePath := ".") : IO (Option String) := do
  let out ← IO.Process.output
    {cmd := "git", args := #["merge-base", "HEAD", targetRef], cwd := cwd}
  if out.exitCode == 0 then
    pure (some out.stdout.trimAscii.toString)
  else
    -- merge-base failed (target ref not reachable); return none to signal cap-only walk
    pure none

/--
Return `true` if `HEAD` is an ancestor of (or equal to) the local `master`
branch — i.e. the current commit is already part of master's history and has no
fork-specific divergence.

Uses `git merge-base --is-ancestor HEAD master`, which exits 0 when HEAD is an
ancestor of master and 1 when it is not. Any other outcome (e.g. `master` not
present locally, or git unavailable) is treated as "not an ancestor", so callers
degrade to their default behavior rather than throwing — matching the never-throw
posture of the rest of the read path.
-/
def headIsAncestorOfMaster (cwd : FilePath := ".") : IO Bool := do
  try
    let out ← IO.Process.output
      {cmd := "git", args := #["merge-base", "--is-ancestor", "HEAD", "master"], cwd := cwd}
    pure (out.exitCode == 0)
  catch _ =>
    pure false

/--
Probe a single container for the per-SHA marker blob.

Issues an anonymous HEAD against `{container}/m/{repo}/{sha}` and returns
`true` iff the response is 200. The marker is uploaded by `put-staged`
after a successful upload, so its existence is a reliable "this commit
was fully cached" signal.

Cheaper than blob-listing: deterministic URL, headers-only response,
billed as a Read op.
-/
def probeContainerForSHA (container : Container) (repo sha : String) :
    IO Bool := do
  let url := markerURL container repo sha
  -- Discard the response body to the platform null device (`NUL` on Windows),
  -- so curl reports a write error only on a genuine failure, not on every probe.
  let out ← IO.Process.output
    {cmd := (← IO.getCurl),
     args := #["-s", "-o", IO.nullDevice, "-w", "%{http_code}", "-I", url],
     cwd := "."}
  if out.exitCode != 0 then
    -- Network error; assume no cache at this SHA
    pure false
  else
    pure (out.stdout.trimAscii.toString == "200")

/-- Default number of marked fork commits `cache get --unsafe` will try as SHA
scopes: 1, namely just the latest cached SHA. Overridden by
`--unsafe-window=N`. -/
def defaultUnsafeSHAWindow : Nat := 1

/--
Walk a list of SHAs (most recent first) and collect up to `limit` of them whose
per-SHA marker exists in the `forks` container. Stops early once `limit` are
found, so at most `limit` probes succeed (and at most `shas.length` are made).

`forks` is the only SHA-scoped container; master/nightly-testing/pr-toolchain-tests
are not scoped, so probing them here would be meaningless.
-/
def findRecentSHAsWithCache (shas : List String) (repo : String) (limit : Nat) :
    IO (List String) := do
  let container := Container.forks
  let mut found : Array String := #[]
  for sha in shas do
    if found.size ≥ limit then break
    if ← probeContainerForSHA container repo sha then
      found := found.push sha
  pure found.toList

/--
Given a list of SHAs, find the most recent one that has cached entries in the
forks container under the SHA-scoped namespace. Returns the first SHA the probe
accepts, or none if none are found.
-/
def findMostRecentSHAWithCache (shas : List String) (repo : String) :
    IO (Option String) :=
  return (← findRecentSHAsWithCache shas repo 1).head?

/--
Resolve a git ref (HEAD, branch name, tag, short SHA, full SHA) to a full
commit SHA via `git rev-parse`. Errors propagate if the ref is unknown.
-/
def resolveGitRef (ref : String) (cwd : FilePath := ".") : IO String := do
  let out ← IO.Process.output {cmd := "git", args := #["rev-parse", ref], cwd := cwd}
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"git rev-parse {ref} failed (exit code {out.exitCode}):\n{out.stderr.trimAscii}"
  pure out.stdout.trimAscii.toString

/--
Resolve the repo to use for a `cache query` invocation.

Precedence: the explicit `--repo=` flag (if passed) > the cwd's git remote
> `MATHLIBREPO`. Defaulting to the git remote is intentional for `query` —
the typical user is asking "what's cached for *my* commits", not for
canonical mathlib's commits.
-/
def resolveQueryRepo (repoExplicit? : Option String) : IO String := do
  match repoExplicit? with
  | some r => pure r
  | none =>
    match ← getRemoteRepo "." with
    | some info => pure info.repo
    | none => pure MATHLIBREPO

/--
Boolean probe for a single commit: prints `cached` or `not cached` and exits
with status 0 / 1 respectively. Intended for scripting.

Probes the `forks` per-SHA marker, the only SHA-scoped container. Canonical repos
have no per-commit namespace, so it exits non-zero with a note instead of a
misleading `not cached`.
-/
def cacheQuerySingle (repo sha : String) : IO Unit := do
  if isCanonicalRepo repo then
    IO.eprintln s!"{repo} caches by file hash, not per commit, so there is no per-commit build to query."
    (← IO.getStderr).flush
    IO.Process.exit 1
  let cached ← probeContainerForSHA Container.forks repo sha
  if cached then
    IO.println s!"cached: {sha}"
  else
    IO.println s!"not cached: {sha}"
    (← IO.getStdout).flush
    IO.Process.exit 1

/--
Implement the `cache query` subcommand.

Walks git log backwards from HEAD, stopping at the merge base with `master`
(or a hard cap if the merge base is not reachable), and probes each commit's
SHA-scoped namespace to find the most recent commit that has cache entries.

This is a diagnostic-only command: it prints the SHA to stdout but does not
auto-apply it. The user manually passes the result to `cache get` if desired.
-/
def cacheQuery (repo : String) (cap : Nat := 50) (cwd : FilePath := ".") : IO Unit := do
  if isCanonicalRepo repo then
    IO.println s!"`cache query` locates a fork PR's per-commit cache. {repo} reads \
      its own cache container directly, so there is nothing to query for it."
    return
  -- Determine merge base with master. If not reachable, use cap-only walk.
  let mergeBase? ← gitMergeBase "master" cwd
  let stopRef := mergeBase?.getD ""

  -- Walk git log backwards from HEAD.
  let shas ← gitLogWalk "HEAD" stopRef cap cwd
  if shas.isEmpty then
    IO.println "No commits found to walk (repository history is empty)"
    return

  -- Probe each SHA in order (most recent first).
  let found? ← findMostRecentSHAWithCache shas repo
  match found? with
  | some sha =>
    IO.println s!"Most recent cached commit on this branch for fork {repo}: {sha}"
    IO.println s!""
    IO.println s!"To use this cache, run:"
    IO.println s!"  lake exe cache get --scope={sha}"
    IO.println s!""
    IO.println s!"Note: this means trusting the artifacts built at that commit;"
    IO.println s!"`cache get` will print a security notice when --scope is set."
  | none =>
    IO.println s!"No cached CI build found for fork {repo} within the last {cap} commits on this branch."
    IO.println s!"This usually means CI hasn't built any of these commits yet."

/--
Discover the SHA scopes `cache get --unsafe` should try, most recent first.

Walks git history from HEAD back to the merge base with `master` (or a hard
`cap` if the merge base is not reachable) and returns up to `window` commit SHAs
whose per-SHA marker exists in the `forks` container — i.e. the most recent
`window` commits on this branch that CI has fully cached for this fork.

Unlike `cacheQuery`, this is consumed automatically by `cache get` rather than
printed for the user, and it returns several SHAs instead of one. An empty
result means no cached commit was found in range; the caller falls back to a
normal (unscoped) read.
-/
def discoverUnsafeScopes (repo : String) (window : Nat := defaultUnsafeSHAWindow)
    (cap : Nat := 50) (cwd : FilePath := ".") : IO (List String) := do
  let mergeBase? ← gitMergeBase "master" cwd
  let stopRef := mergeBase?.getD ""
  let shas ← gitLogWalk "HEAD" stopRef cap cwd
  findRecentSHAsWithCache shas repo window

end Cache.Requests
