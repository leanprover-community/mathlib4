/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# The fork per-commit probes

The developer workflow's mechanisms over a fork's per-commit markers: the
`cache query` walk that finds the most recent commit on the current branch
with a cached CI build, the single-commit probe, and the `--unsafe` walk that
collects cached commits to read at. All walk git history back to the merge
base with `master` and probe each commit's marker with one HEAD request; none
reads or writes artifacts.
-/

namespace Cache.Workflow.Developer

open Cache.Requests

open System (FilePath)

/--
The developer cache's read host: the bucket that holds the `forks` container,
read directly rather than through the cache resolver. The workflow reads its
other containers through the public endpoint (`publicCacheEndpoint`).
-/
def developerCacheEndpoint : String := "https://r2devcache.mathlib.org"

/-- The read URL of each container in a developer read: `forks` on the
developer cache's host, every other container on the public endpoint, both
under the read base rule (`Container.readURL`). -/
def readURL (c : Container) : IO String :=
  c.readURL (if c == .forks then developerCacheEndpoint else publicCacheEndpoint)

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
Whether CI cached commit `sha` of fork `repo`: an anonymous HEAD against the
marker `forks/m/{repo}/{sha}` (`markerReadURL`) answers 200. The marker is
uploaded by `put-staged` after a successful upload, so its existence is a
reliable "this commit was fully cached" signal.

Cheaper than blob-listing: deterministic URL, headers-only response,
billed as a Read op.
-/
def probeCommit (repo sha : String) : IO Bool := do
  let url := markerReadURL (← readURL .forks) repo sha
  -- Discard the response body to the platform null device (`NUL` on Windows),
  -- so curl reports a write error only on a genuine failure, not on every probe.
  let out ← IO.Process.output
    {cmd := (← IO.getCurl),
     args := #["-s", "-o", IO.nullDevice, "-w", "%{http_code}", "-I"] ++
       -- No retry flags: the probe is diagnostic and a false negative is
       -- cheap. The time bounds keep an unreachable endpoint from stalling
       -- the up-to-50-probe `cache query` walk.
       curlFollowRedirectArgs ++
       #["--connect-timeout", "10", "--max-time", "30", url],
     cwd := "."}
  if out.exitCode != 0 then
    -- Network error; assume no cache at this SHA
    pure false
  else
    pure (out.stdout.trimAscii.toString == "200")

/--
Walk a list of SHAs (most recent first) and collect up to `limit` of them whose
per-SHA marker exists in the `forks` container. Stops early once `limit` are
found, so at most `limit` probes succeed (and at most `shas.length` are made).

`forks` is the only SHA-scoped container; master/nightly-testing/pr-toolchain-tests
are not scoped, so probing them here would be meaningless.
-/
def findRecentSHAsWithCache (shas : List String) (repo : String) (limit : Nat) :
    IO (List String) := do
  let mut found : Array String := #[]
  for sha in shas do
    if found.size ≥ limit then break
    if ← probeCommit repo sha then
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
Boolean probe for a single commit: prints `cached` or `not cached` and exits
with status 0 / 1 respectively. Intended for scripting.

Probes the `forks` per-SHA marker, the only SHA-scoped container; `repo` is a
fork.
-/
def cacheQuerySingle (repo sha : String) : IO Unit := do
  let cached ← probeCommit repo sha
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
`repo` is a fork.
-/
def cacheQuery (repo : String) (cap : Nat := 50) (cwd : FilePath := ".") : IO Unit := do
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
def discoverUnsafeScopes (repo : String) (window : Nat)
    (cap : Nat := 50) (cwd : FilePath := ".") : IO (List String) := do
  let mergeBase? ← gitMergeBase "master" cwd
  let stopRef := mergeBase?.getD ""
  let shas ← gitLogWalk "HEAD" stopRef cap cwd
  findRecentSHAsWithCache shas repo window

end Cache.Workflow.Developer
