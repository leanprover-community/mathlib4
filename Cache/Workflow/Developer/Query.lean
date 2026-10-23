/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Requests
public import Cache.Marker

/-!
# The `cache query` subcommand

Discovers the most recent commit on the current branch that has a cached CI
build, by walking git history back to the merge base with `master` and probing
each commit's per-SHA marker. Git lookups use
`CacheM.Context.mathlibDepPath`. The command prints a SHA for the user to pass
to `cache get --scope=`, and never reads or writes artifacts itself. The
markers live in the `forks` container under the read base the developer-cache
workflow gives it (`forksBase`).
-/

public section

namespace Cache.Workflow.Developer

open Cache.Requests

/--
Walk git log backwards from HEAD, starting from `startRef`, stopping at
`stopRef` or after `cap` commits (whichever comes first).

Returns the list of commit SHAs in reverse chronological order (most recent first).
-/
def gitLogWalk (startRef stopRef : String) (cap : Nat) :
    IO.CacheM (List String) := do
  -- Construct git log command: walk from startRef to stopRef (if provided) using first-parent.
  -- First-parent follows the main branch across merges, which is the intended behavior.
  let args := if stopRef.isEmpty then
    #["log", startRef, "--first-parent", "--pretty=format:%H", s!"--max-count={cap}"]
  else
    #["log", s!"{startRef}...{stopRef}", "--first-parent", "--pretty=format:%H", s!"--max-count={cap}"]
  let out ← IO.Process.output {cmd := "git", args := args, cwd := (← read).mathlibDepPath}
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"git log failed (exit code {out.exitCode}):\n{out.stderr.trimAscii}"
  let shas := out.stdout.trimAscii.toString.splitOn "\n" |>.filter (· ≠ "")
  pure shas

/--
Determine the merge base between `HEAD` and a target ref (typically `master`).
Falls back to a cap-only walk if the ref is not reachable.
-/
def gitMergeBase (targetRef : String) : IO.CacheM (Option String) := do
  let out ← IO.Process.output
    {cmd := "git", args := #["merge-base", "HEAD", targetRef], cwd := (← read).mathlibDepPath}
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
def headIsAncestorOfMaster : IO.CacheM Bool := do
  try
    let out ← IO.Process.output
      {cmd := "git", args := #["merge-base", "--is-ancestor", "HEAD", "master"],
       cwd := (← read).mathlibDepPath}
    pure (out.exitCode == 0)
  catch _ =>
    pure false

/-- Check the marker of `sha` in the `forks` container under the read base
`forksBase`. -/
def probeForksForSHA (forksBase repo sha : String) : IO Bool :=
  checkMarker (Container.forks.location forksBase repo (some sha))

/-- Default number of marked fork commits `cache get --unsafe` will try as SHA
scopes: 1, namely just the latest cached SHA. Overridden by
`--unsafe-window=N`. -/
def defaultUnsafeSHAWindow : Nat := 1

/--
Walk a list of SHAs (most recent first) and collect up to `limit` of them whose
per-SHA marker exists in the `forks` container. Stops early once `limit` are
found, so at most `limit` probes succeed (and at most `shas.length` are made).

`forks` is the only SHA-scoped container; `master` is flat, so probing it here
would be meaningless.
-/
def findRecentSHAsWithCache (forksBase : String) (shas : List String) (repo : String)
    (limit : Nat) : IO (List String) := do
  let mut found : Array String := #[]
  for sha in shas do
    if found.size ≥ limit then break
    if ← probeForksForSHA forksBase repo sha then
      found := found.push sha
  pure found.toList

/--
Given a list of SHAs, find the most recent one that has cached entries in the
forks container under the SHA-scoped namespace. Returns the first SHA the probe
accepts, or none if none are found.
-/
def findMostRecentSHAWithCache (forksBase : String) (shas : List String) (repo : String) :
    IO (Option String) :=
  return (← findRecentSHAsWithCache forksBase shas repo 1).head?

/--
Boolean probe for a single commit: prints `cached` or `not cached` and returns
the exit status 0 / 1 respectively. Intended for scripting.

Probes the `forks` per-SHA marker, the only SHA-scoped container; `repo` is a
fork.
-/
def cacheQuerySingle (forksBase repo sha : String) : IO UInt32 := do
  if ← probeForksForSHA forksBase repo sha then
    IO.println s!"cached: {sha}"
    return 0
  else
    IO.println s!"not cached: {sha}"
    return 1

/--
Implement the `cache query` subcommand.

Walks git log backwards from HEAD, stopping at the merge base with `master`
(or a hard cap if the merge base is not reachable), and probes each commit's
SHA-scoped namespace to find the most recent commit that has cache entries.

This is a diagnostic-only command: it prints the SHA to stdout but does not
auto-apply it. The user manually passes the result to `cache get` if desired.
`repo` is a fork.
-/
def cacheQuery (forksBase repo : String) (cap : Nat := 50) : IO.CacheM Unit := do
  -- Determine merge base with master. If not reachable, use cap-only walk.
  let mergeBase? ← gitMergeBase "master"
  let stopRef := mergeBase?.getD ""

  -- Walk git log backwards from HEAD.
  let shas ← gitLogWalk "HEAD" stopRef cap
  if shas.isEmpty then
    IO.println "No commits found to walk (repository history is empty)"
    return

  -- Probe each SHA in order (most recent first).
  let found? ← findMostRecentSHAWithCache forksBase shas repo
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
    IO.println s!"No commit-specific cache found for fork {repo} within the last {cap} commits on this branch."
    IO.println "Simply call:"
    IO.println "  lake exe cache get"
    IO.println "If CI is still building your latest commit, call it again after CI finishes."

/--
Discover the SHA scopes `cache get --unsafe` should try, most recent first.

Walks git history from HEAD back to the merge base with `master` (or a hard
`cap` if the merge base is not reachable) and returns up to `window` commit SHAs
whose per-SHA marker exists in the `forks` container — i.e. the most recent
`window` commits on this branch that CI has fully cached for this fork.

Unlike `cacheQuery`, this is consumed automatically by `cache get` rather than
printed for the user, and it returns several SHAs instead of one. An empty
result means no cached commit was found in range; the caller falls back to a
normal read, which reads the `forks` namespace of the checked-out HEAD.
-/
def discoverUnsafeScopes (forksBase repo : String) (window : Nat := defaultUnsafeSHAWindow)
    (cap : Nat := 50) : IO.CacheM (List String) := do
  let mergeBase? ← gitMergeBase "master"
  let stopRef := mergeBase?.getD ""
  let shas ← gitLogWalk "HEAD" stopRef cap
  findRecentSHAsWithCache forksBase shas repo window

end Cache.Workflow.Developer
