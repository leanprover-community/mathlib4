/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Marcelo Lynch
-/

import Cache.Infra

/-!
# Which repository's cache

The GitHub repository a cache read is for: detection from the git remote of
the mathlib checkout (`getRemoteRepo`), and the resolution rules that turn a
detection and an explicit `--repo=` into the repo the read uses
(`resolveRepo`). The workflow decision (`Cache.Workflow`) starts from this
resolved repo. `resolveGitRef` is the git-ref helper the commands share.
-/

namespace Cache.Requests

open System (FilePath)

/-- The `owner/repo` name in a git remote URL. -/
def extractRepoFromUrl (url : String) : Option String := do
  let url := url.dropSuffix ".git"
  let pos ← url.revFind? (· == '/')
  let pos ← (url.sliceTo pos).revFind? (fun c => c == '/' || c == ':')
  return url.sliceFrom (String.Slice.Pos.ofSliceTo pos).next! |>.copy

/-- Spot check if a URL is valid for a git remote -/
def isRemoteURL (url : String) : Bool :=
  "https://".isPrefixOf url || "http://".isPrefixOf url || "git@github.com:".isPrefixOf url

/-- The `owner/repo` name of the remote `remoteName` of the checkout at
`mathlibDepPath`; `remoteName` may itself be a URL (as after `gh pr checkout`).
Prints a warning and returns `none` when git or the URL gives no answer. -/
def getRepoFromRemote (mathlibDepPath : FilePath) (remoteName : String) (errorContext : String) : IO (Option String) := do
  -- If the remote is already a valid URL, attempt to extract the repo from it. This happens with `gh pr checkout`
  if isRemoteURL remoteName then
    repoFromURL remoteName
  else
  -- If not, we use `git remote get-url` to find the URL of the remote. This assumes the remote has a
  -- standard name like `origin` or `upstream` or it errors out.
  let out ← IO.Process.output
    {cmd := "git", args := #["remote", "get-url", remoteName], cwd := mathlibDepPath}
  -- If `git remote get-url` fails then return none.
  let output := out.stdout.trimAscii
  unless out.exitCode == 0 do
    IO.println s!"\
      Warning: failed to run Git to determine Mathlib's repository from {remoteName} remote\n\
      {errorContext}\n\
      Continuing to fetch the cache from {MATHLIBREPO}."
    return none
  -- Finally attempt to extract the repository from the remote URL returned by `git remote get-url`
  repoFromURL output.copy
where repoFromURL (url : String) : IO (Option String) := do
    if let some repo := extractRepoFromUrl url then
      return some repo
    else
      IO.println s!"\
        Warning: Failed to extract repository from remote URL: {url}.\n\
        {errorContext}\n\
        Continuing to fetch the cache from {MATHLIBREPO}."
      return none

/-- Check if we're in a detached HEAD state at a nightly-testing tag -/
def isDetachedAtNightlyTesting (mathlibDepPath : FilePath) : IO Bool := do
  -- Get the current commit hash and check if it's a nightly-testing tag
  let currentCommit ← IO.Process.output
    {cmd := "git", args := #["rev-parse", "HEAD"], cwd := mathlibDepPath}
  if currentCommit.exitCode == 0 then
    let commitHash := currentCommit.stdout.trimAscii.copy
    let tagInfo ← IO.Process.output
      {cmd := "git", args := #["name-rev", "--tags", commitHash], cwd := mathlibDepPath}
    if tagInfo.exitCode == 0 then
      let parts := tagInfo.stdout.trimAscii.copy.splitOn " "
      -- git name-rev returns "commit_hash tags/tag_name" or just "commit_hash undefined" if no tag
      if parts.length >= 2 && parts[1]!.startsWith "tags/" then
        let tagName := parts[1]!.drop 5  -- Remove "tags/" prefix
        return tagName.startsWith "nightly-testing-"
      else
        return false
    else
      return false
  else
    return false

/--
Inner implementation: may throw if git is unavailable or the directory has no
git checkout. Callers should use `getRemoteRepo` instead.
-/
private def getRemoteRepoImpl (mathlibDepPath : FilePath) : IO (Option String) := do

  -- The nightly-testing repository's branches, and a detached checkout at one
  -- of its tags, use that repository's cache. Every other checkout uses the
  -- remote its branch tracks.
  let currentBranch ← IO.Process.output
    {cmd := "git", args := #["rev-parse", "--abbrev-ref", "HEAD"], cwd := mathlibDepPath}

  if currentBranch.exitCode == 0 then
    let branchName := currentBranch.stdout.trimAscii.dropPrefix "heads/"
    IO.println s!"Current branch: {branchName}"

    -- Check if we're in a detached HEAD state at a nightly-testing tag
    let isDetachedAtNightlyTesting ← if branchName == "HEAD".toSlice then
      isDetachedAtNightlyTesting mathlibDepPath
    else
      pure false

    -- Check if we're on a branch that should use nightly-testing remote
    let shouldUseNightlyTesting := branchName == "nightly-testing".toSlice ||
                                  branchName.startsWith "lean-pr-testing-" ||
                                  branchName.startsWith "batteries-pr-testing-" ||
                                  branchName.startsWith "bump/" ||
                                  isDetachedAtNightlyTesting

    if shouldUseNightlyTesting then
      let repo := "leanprover-community/mathlib4-nightly-testing"
      IO.println s!"Using cache from nightly-testing remote: {repo}"
      return some repo

  -- Fall back to using the remote that the current branch is tracking
  let trackingRemote ← IO.Process.output
    {cmd := "git", args := #["config", "--get", s!"branch.{currentBranch.stdout.trimAscii}.remote"], cwd := mathlibDepPath}

  let remoteName := if trackingRemote.exitCode == 0 then
    trackingRemote.stdout.trimAscii.copy
  else
    -- If no tracking remote is configured, fall back to origin
    "origin"

  let repo? ← getRepoFromRemote mathlibDepPath remoteName
    s!"Ensure Git is installed and the '{remoteName}' remote points to its GitHub repository."
  match repo? with
  | some repo =>
    IO.println s!"Using cache from {remoteName}: {repo}"
    return some repo
  | none =>
    IO.println s!"Using cache from {MATHLIBREPO}."
    return none

/--
The GitHub repository of a Mathlib checkout, from its git remote: the
nightly-testing repository on its branches and tags, else the repository the
tracked remote points at.

Returns `none` if git is unavailable, the path is not inside a git checkout, or
the remote cannot be resolved. This is the expected outcome when `cache get` is
invoked on a dependency that was fetched as an archive rather than a git clone;
callers fall back to `MATHLIBREPO`.
-/
def getRemoteRepo (mathlibDepPath : FilePath) : IO (Option String) := do
  try
    return (← getRemoteRepoImpl mathlibDepPath)
  catch _ =>
    return none

/--
The repo a read in a project that depends on Mathlib resolves to, given what
the dependency checkout's git remote reports.

Only a canonical detection is honored: a project whose mathlib dependency is
the nightly-testing repo (or is pinned to a `nightly-testing-*` tag, which
the probe also reports as that repo) reads the nightly cache, because its
artifacts exist nowhere else. Everything else — a fork remote, or no
detection at all — resolves to `MATHLIBREPO`, so a dependency checkout's
remote can never steer a downstream read into a fork's artifacts. An explicit
`--repo=` is the opt-in for that; `resolveRepo` applies it before this
function is consulted.
-/
def resolveDownstreamRepo (detected? : Option String) : String :=
  match detected? with
  | some repo => if isCanonicalRepo repo then repo else MATHLIBREPO
  | none => MATHLIBREPO

/--
Resolve the GitHub repo for cache reads from a single `getRemoteRepo` probe.

Returns `(detectedRepo?, resolvedRepo)`:
* `detectedRepo?` is what the git remote reports (`none` if it can't be
  determined); the warning path compares it against an explicit `--repo=` to
  tell whether the user is overriding the checkout's repo.
* `resolvedRepo` is what the read path uses. An explicit `--repo=` wins. On a
  mathlib checkout (`isMathlibRoot`, canonical or fork) the detection is next,
  then `MATHLIBREPO`. In a project that depends on Mathlib the detection goes
  through `resolveDownstreamRepo`: only a canonical repo is honored, so a fork
  remote on the dependency checkout cannot take the read off the public cache.

`getRemoteRepo` shells out to git and prints branch/remote diagnostics;
resolving here lets the read path, the warning, and the HEAD hint share a
single probe keyed on `mathlibDepPath`.
-/
def resolveRepo (repo? : Option String) (mathlibDepPath : FilePath) (isMathlibRoot : Bool) :
    IO (Option String × String) := do
  let detected? ← getRemoteRepo mathlibDepPath
  if let some repo := repo? then
    return (detected?, repo)
  if isMathlibRoot then
    return (detected?, detected?.getD MATHLIBREPO)
  let resolved := resolveDownstreamRepo detected?
  -- The probe above prints "Using cache from ...: {detected}"; correct the
  -- record when the downstream resolution discards that detection.
  if detected?.isSome && detected? != some resolved then
    IO.println s!"Dependency checkout points at {detected?.get!}; a project \
      using Mathlib reads the {resolved} cache (pass --repo to override)."
  return (detected?, resolved)

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

end Cache.Requests
