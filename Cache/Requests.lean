/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Batteries.Data.String.Matcher
import Cache.Hashing
import Cache.Infra
import Lake.Load.Manifest

namespace Cache.Requests

open System (FilePath)

/--
Resolved repository identity for cache lookups.
-/
structure RepoInfo where
  repo : String
  deriving Repr

/--
Helper function to extract repository name from a git remote URL
-/
def extractRepoFromUrl (url : String) : Option String := do
  let url := url.dropSuffix ".git"
  let pos ← url.revFind? (· == '/')
  let pos ← (url.sliceTo pos).revFind? (fun c => c == '/' || c == ':')
  return url.sliceFrom (String.Slice.Pos.ofSliceTo pos).next! |>.copy

/-- Spot check if a URL is valid for a git remote -/
def isRemoteURL (url : String) : Bool :=
  "https://".isPrefixOf url || "http://".isPrefixOf url || "git@github.com:".isPrefixOf url

/--
Helper function to get repository from a remote name
-/
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

/--
Finds the remote name that points to `leanprover-community/mathlib4` repository.
Returns the remote name and prints warnings if the setup doesn't follow conventions.
-/
def findMathlibRemote (mathlibDepPath : FilePath) : IO String := do
  let remotesInfo ← IO.Process.output
    {cmd := "git", args := #["remote", "-v"], cwd := mathlibDepPath}

  unless remotesInfo.exitCode == 0 do
    throw <| IO.userError s!"\
      Failed to run Git to list remotes (exit code: {remotesInfo.exitCode}).\n\
      Ensure Git is installed.\n\
      Stdout:\n{remotesInfo.stdout.trimAscii}\nStderr:\n{remotesInfo.stderr.trimAscii}\n"

  let remoteLines := remotesInfo.stdout.splitToList (· == '\n')
  let mut mathlibRemote : Option String := none
  let mut originPointsToMathlib : Bool := false

  for line in remoteLines do
    let parts := line.trimAscii.copy.splitToList (· == '\t')
    if parts.length >= 2 then
      let remoteName := parts[0]!
      let remoteUrl := parts[1]!.takeWhile (· != ' ') |>.copy -- Remove (fetch) or (push) suffix

      -- Check if this remote points to leanprover-community/mathlib4
      let isMathlibRepo := remoteUrl.contains "leanprover-community/mathlib4"

      if isMathlibRepo then
        if remoteName == "origin" then
          originPointsToMathlib := true
        mathlibRemote := some remoteName

  match mathlibRemote with
  | none =>
    throw <| IO.userError "Could not find a remote pointing to leanprover-community/mathlib4"
  | some remoteName =>
    if remoteName != "upstream" then
      let mut warning := s!"Some Mathlib ecosystem tools assume that the git remote for `leanprover-community/mathlib4` is named `upstream`. You have named it `{remoteName}` instead. We recommend changing the name to `upstream`."
      if originPointsToMathlib then
        warning := warning ++ " Moreover, `origin` should point to your own fork of the mathlib4 repository."
      warning := warning ++ " You can set this up with `git remote add upstream https://github.com/leanprover-community/mathlib4.git`."
      IO.println s!"Warning: {warning}"
    return remoteName

/--
Extracts PR number from a git ref like "refs/remotes/upstream/pr/1234"
-/
def extractPRNumber (ref : String) : Option Nat := do
  let parts := ref.splitToList (· == '/')
  if parts.length >= 2 && parts[parts.length - 2]! == "pr" then
    let prStr := parts[parts.length - 1]!
    prStr.toNat?
  else
    none

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
Attempts to determine the GitHub repository of a version of Mathlib from its Git remote.
If the current commit coincides with a PR ref, it will determine the source fork
of that PR rather than just using the origin remote.
-/
def getRemoteRepo (mathlibDepPath : FilePath) : IO (Option RepoInfo) := do

  -- Since currently we need to push a PR to `leanprover-community/mathlib` build a user cache,
  -- we check if we are a special branch or a branch with PR. This leaves out non-PRed fork
  -- branches. These should be covered if we ever change how the cache is uploaded from forks
  -- to obviate the need for a PR.
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
      return some {repo := repo}

    -- Only search for PR refs if we're not on a regular branch like master, bump/*, or nightly-testing*
    -- let isSpecialBranch := branchName == "master" || branchName.startsWith "bump/" ||
    --                       branchName.startsWith "nightly-testing"

    -- TODO: this code is currently broken in two ways: 1. you need to write `%(refname)` in quotes and
    -- 2. it is looking in the wrong place when in detached HEAD state.
    -- We comment it out for now, but we should fix it later.
    -- Check if the current commit coincides with any PR ref
    -- if !isSpecialBranch then
    --   let mathlibRemoteName ← findMathlibRemote mathlibDepPath
    --   let currentCommit ← IO.Process.output
    --     {cmd := "git", args := #["rev-parse", "HEAD"], cwd := mathlibDepPath}
    --
    --   if currentCommit.exitCode == 0 then
    --     let commit := currentCommit.stdout.trim
    --     -- Get all PR refs that contain this commit
    --     let prRefPattern := s!"refs/remotes/{mathlibRemoteName}/pr/*"
    --     let refsInfo ← IO.Process.output
    --       {cmd := "git", args := #["for-each-ref", "--contains", commit, prRefPattern, "--format=%(refname)"], cwd := mathlibDepPath}
    --     -- The code below is for debugging purposes currently
    --     IO.println s!"`git for-each-ref --contains {commit} {prRefPattern} --format=%(refname)` returned:
    --     {refsInfo.stdout.trim} with exit code {refsInfo.exitCode} and stderr: {refsInfo.stderr.trim}."
    --     let refsInfo' ← IO.Process.output
    --       {cmd := "git", args := #["for-each-ref", "--contains", commit, prRefPattern, "--format=\"%(refname)\""], cwd := mathlibDepPath}
    --     IO.println s!"`git for-each-ref --contains {commit} {prRefPattern} --format=\"%(refname)\"` returned:
    --     {refsInfo'.stdout.trim} with exit code {refsInfo'.exitCode} and stderr: {refsInfo'.stderr.trim}."
    --
    --     if refsInfo.exitCode == 0 && !refsInfo.stdout.trim.isEmpty then
    --       let prRefs := refsInfo.stdout.trim.split (· == '\n')
    --       -- Extract PR numbers from refs like "refs/remotes/upstream/pr/1234"
    --       for prRef in prRefs do
    --         if let some prNumber := extractPRNumber prRef then
    --           -- Get PR details using gh
    --           let prInfo ← IO.Process.output
    --             {cmd := "gh", args := #["pr", "view", toString prNumber, "--json", "headRefName,headRepositoryOwner,number"], cwd := mathlibDepPath}
    --           if prInfo.exitCode == 0 then
    --             if let .ok json := Lean.Json.parse prInfo.stdout.trim then
    --               if let .ok owner := json.getObjValAs? Lean.Json "headRepositoryOwner" then
    --                 if let .ok login := owner.getObjValAs? String "login" then
    --                   if let .ok repoName := json.getObjValAs? String "headRefName" then
    --                     if let .ok prNum := json.getObjValAs? Nat "number" then
    --                       let repo := s!"{login}/mathlib4"
    --                       IO.println s!"Using cache from PR #{prNum} source: {login}/{repoName} (commit {commit.take 8} found in PR ref)"
    --                       let useFirst := if login != "leanprover-community" then true else false
    --                       return {repo := repo, useFirst := useFirst}

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
    IO.println s!"Using cache from {remoteName}: {repo?}"
    return some {repo := repo}
  | none =>
    IO.println s!"Using cache from {MATHLIBREPO}."
    return none

/--
Process-wide override for the container fallback list, set by the `--cache-from`
CLI flag. When `none`, downloads use `defaultContainersForRepo`; when `some cs`,
all repos use `cs` instead.
-/
initialize cacheFromOverride : IO.Ref (Option (List Container)) ← IO.mkRef none

/--
URL to use for read-only Azure operations that aren't yet multi-container-aware
(e.g. `getFilesInfo`). Always points at the master container.
-/
def masterContainerURL : String := Container.master.azureURL

/--
Compute the trust-ordered list of container base URLs to try when downloading
files for a given GitHub repo.

Precedence (most specific wins):
1. `MATHLIB_CACHE_GET_URL` env var, if set, returns a single anonymous URL
   (single-URL escape hatch — bypasses multi-container logic entirely).
2. `--cache-from` CLI override (set via `cacheFromOverride`). The most
   deliberate signal — a user explicitly typing it at the call site.
3. `MATHLIB_CACHE_FROM` env var (comma-separated container list, same
   shape as `--cache-from`). This is how CI workflows widen the lookup
   chain to match their trust-dispatched write target without editing
   every `cache get` call. Branch-class-aware trust dispatch lives in
   YAML, not here — see `build_template.yml`.
4. `defaultContainersForRepo repo` — the repo-level fallback that runs on
   any machine (CI or user) when no override is set.
-/
def effectiveGetURLs (repo : String) : IO (List (Option Container × String)) := do
  if let some url ← IO.getEnv "MATHLIB_CACHE_GET_URL" then
    return [(none, url)]
  let cliOverride? ← cacheFromOverride.get
  let envOverride? ← do
    match (← IO.getEnv "MATHLIB_CACHE_FROM") with
    | none => pure none
    | some s =>
      match parseCacheFromList s with
      | some cs => pure (some cs)
      | none =>
        IO.eprintln s!"Warning: ignoring MATHLIB_CACHE_FROM={s} \
          (unrecognized container name). Known containers: \
          {", ".intercalate (Container.all.map Container.name)}."
        pure none
  let containers :=
    cliOverride?.getD (envOverride?.getD (defaultContainersForRepo repo))
  return containers.map fun c => (some c, c.azureURL)

/-- Authentication method used for cache upload operations. -/
inductive UploadAuth where
  | azureSas (token : String)
  | azureBearer (token : String)

/-- Retrieves upload credentials from the environment. -/
def getUploadAuth : IO UploadAuth := do
  if let some token ← IO.getEnv "MATHLIB_CACHE_AZURE_BEARER_TOKEN" then
    let token := token.trimAscii.copy
    if !token.isEmpty then
      return .azureBearer token
  if let some token ← IO.getEnv "MATHLIB_CACHE_SAS" then
    let token := token.trimAscii.copy
    if !token.isEmpty then
      return .azureSas token
  throw <| IO.userError
    "environment variable MATHLIB_CACHE_AZURE_BEARER_TOKEN or MATHLIB_CACHE_SAS must be set to upload caches"

/--
Construct the URL for the cache file `fileName` in repo `repo`, against the
container reachable at `containerURL`.

The `f/` prefix marks files (vs commits, which use `c/`). Whether the rest of
the path is flat (`/f/<fileName>`) or namespaced by repo (`/f/<repo>/<fileName>`)
is decided by the *container*, not the repo (see `Container.flatPath`):
the same hash uploaded under `repo = MATHLIBREPO` lands flat in `master` and
prefixed in `forks`, because the trust-classified containers have to be
unambiguous across all their writers — including canonical-repo writers
whose trust level is fork-equivalent (e.g. `ci-dev/*`, `bors trying`).

`container` is `none` only in the `MATHLIB_CACHE_GET_URL` /
`MATHLIB_CACHE_PUT_URL` escape-hatch path, where the URL is user-supplied and
we don't know which container's policy to apply; we fall back to the legacy
"flat for canonical, prefixed otherwise" rule there so dev/local overrides
behave exactly as they did before the per-container split.
-/
def mkFileURL (container : Option Container) (repo containerURL fileName : String)
    (repoScope : Option String := none) : String :=
  let flat := match container with
    | some c => c.flatPath repo
    | none => repo == MATHLIBREPO
  let pre := if flat then ""
    else match repoScope with
      | some s => s!"{repo}/{s}/"
      | none => s!"{repo}/"
  s!"{containerURL}/f/{pre}{fileName}"

/--
Process-wide override for the per-SHA scope, set by the `--scope=` CLI flag.
When set, it wins over `MATHLIB_CACHE_REPO_SCOPE`. Mirrors the
`cacheFromOverride` pattern.
-/
initialize scopeOverride : IO.Ref (Option String) ← IO.mkRef none

/--
Resolved repo-scope SHA. Precedence: `--scope=` flag > `MATHLIB_CACHE_REPO_SCOPE`
env var > `none`. Both sources mean "the user has explicitly opted into a
SHA-scoped read"; the non-default-scope warning fires for either.
-/
def getRepoScope : IO (Option String) := do
  if let some s ← scopeOverride.get then
    return some s
  let s? ← IO.getEnv "MATHLIB_CACHE_REPO_SCOPE"
  match s? with
  | some s =>
    let trimmed := s.trimAscii.toString
    pure (if trimmed.isEmpty then none else some trimmed)
  | none => pure none

section Get

/-- Formats the config file for `curl`, containing the list of files to be downloaded
from a single container's base URL. -/
def mkGetConfigContent (container : Option Container) (repo containerURL : String)
    (hashMap : IO.ModuleHashMap) : IO String := do
  let scope? ← getRepoScope
  hashMap.toArray.foldlM (init := "") fun acc ⟨_, hash⟩ => do
    let fileName := hash.asLTar
    -- Below we use `String.quote`, which is intended for quoting for use in Lean code
    -- this does not exactly match the requirements for quoting for curl:
    -- ```
    -- If the parameter contains whitespace (or starts with : or =),
    --  the parameter must be enclosed within quotes.
    -- Within double quotes, the following escape sequences are available:
    --  \, ", \t, \n, \r and \v.
    -- A backslash preceding any other letter is ignored.
    -- ```
    -- If this becomes an issue we can implement the curl spec.

    -- Note we append a '.part' to the filenames here,
    -- which `downloadFiles` then removes when the download is successful.
    pure <| acc ++ s!"url = {mkFileURL container repo containerURL fileName scope?}\n\
      -o {(IO.CACHEDIR / (fileName ++ ".part")).toString.quote}\n"

/-- Calls `curl` to download a single file from a specific container to `CACHEDIR`
(`.cache`). Returns `true` on success, `false` on any error including 404. -/
def downloadFile (container : Option Container) (repo containerURL : String)
    (hash : UInt64) : IO Bool := do
  let scope? ← getRepoScope
  let fileName := hash.asLTar
  let url := mkFileURL container repo containerURL fileName scope?
  let path := IO.CACHEDIR / fileName
  let partFileName := fileName ++ ".part"
  let partPath := IO.CACHEDIR / partFileName
  let out ← IO.Process.output
    { cmd := (← IO.getCurl), args := #[url, "--fail", "--silent", "-o", partPath.toString] }
  if out.exitCode = 0 then
    IO.FS.rename partPath path
    pure true
  else
    IO.FS.removeFile partPath
    pure false

/-- Extract hash from filename (e.g., "/path/to/.cache/00012345.ltar" → 0x12345).
    Handles both `.ltar` and `.ltar.part` files using `FilePath.fileStem`. -/
def hashFromFileName (path : FilePath) : Option UInt64 := do
  let some stem := path.fileStem | .none
  -- For .ltar.part files, fileStem gives "hash.ltar"; apply fileStem again to strip .ltar
  let stem := (FilePath.mk (toString stem)).fileStem.getD stem
  (toString stem).parseHexToUInt64?

/-- Decompress a batch of files using a single leantar invocation -/
def decompressBatch (files : Array (FilePath × Lean.Name))
    (force : Bool) (isMathlibRoot : Bool) (mathlibDepPath : FilePath) :
    IO Unit := do
  if files.isEmpty then return

  -- Build JSON config for all files in batch (similar to unpackCache logic)
  let config := files.map fun (path, mod) =>
    if isMathlibRoot || !IO.isFromMathlib mod then
      .str path.toString
    else
      .mkObj [("file", path.toString), ("base", mathlibDepPath.toString)]

  -- Spawn leantar for this batch
  let exitCode ← IO.spawnLeanTarDecompress config force
  if exitCode != 0 then
    let fileList := files.map (fun (p, m) => s!"{m} ({p})") |>.toList |> String.intercalate ", "
    let firstFew := if files.size ≤ 3 then fileList else
      let preview := files.extract 0 3 |>.map (fun (p, m) => s!"{m} ({p})") |>.toList |> String.intercalate ", "
      s!"{preview}, ... and {files.size - 3} more"
    throw <| IO.userError s!"leantar exited with code {exitCode} on batch of {files.size} files: {firstFew}"

/-- Configuration for decompression during download -/
structure DecompConfig where
  hashToMod : Std.HashMap UInt64 Lean.Name  -- filename hash → module name
  force : Bool
  isMathlibRoot : Bool
  mathlibDepPath : FilePath

private structure TransferState where
  last : Nat
  success : Nat
  failed : Nat
  done : Nat
  speed : Nat
  -- Decompression state (only used when decompConfig is set)
  pending : Array (FilePath × Lean.Name)           -- files waiting to be decompressed
  currentTask : Option (Task (Except IO.Error Unit))  -- current leantar task
  lastBatchSize : Nat                              -- size of the last dispatched batch
  decompressed : Nat                               -- total files decompressed
  decompFailed : Nat                               -- total decompression failures

/-- Harvest the result of a completed decompression task, updating counters.
    Returns `(successful, failed, error?)`. -/
def harvestDecompTask (task : Task (Except IO.Error Unit)) (batchSize : Nat)
    (decompressed decompFailed : Nat) : Nat × Nat × Option IO.Error :=
  match task.get with
  | .ok () => (decompressed + batchSize, decompFailed, none)
  | .error e => (decompressed, decompFailed + batchSize, some e)

/-- Dispatch a new decompression batch if there are pending files -/
def dispatchDecompBatch (pending : Array (FilePath × Lean.Name)) (config : DecompConfig)
    : IO (Option (Task (Except IO.Error Unit))) := do
  if pending.isEmpty then return none
  let task ← IO.asTask (decompressBatch pending config.force config.isMathlibRoot config.mathlibDepPath)
  return some task

def monitorCurl (args : Array String) (size : Nat)
    (caption : String) (speedVar : String) (removeOnError := false)
    (decompConfig : Option DecompConfig := none) : IO TransferState := do
  let useAnsi := (← IO.getEnv "TERM").isSome
  let mkStatus (s : TransferState) : String := Id.run do
    let speedStr :=
      if s.speed != 0 then
        s!", {s.speed / 1000} KB/s"
      else ""
    let mut msg := s!"\r{caption}: {s.success} file(s) [attempted {s.done}/{size} = {100*s.done/size}%{speedStr}]"
    -- Add decompression progress if enabled
    if decompConfig.isSome then
      msg := msg ++ s!", Decompressed: {s.decompressed}"
      if s.decompFailed != 0 then
        msg := msg ++ s!" ({s.decompFailed} failed)"
    if s.failed != 0 then
      msg := msg ++ s!", {s.failed} download failed"
    -- Clear to end of line to avoid remnants from longer previous messages
    if useAnsi then
      msg := msg ++ "\x1b[K"
    return msg
  let init : TransferState := ⟨← IO.monoMsNow, 0, 0, 0, 0, #[], none, 0, 0, 0⟩
  let s ← IO.runCurlStreaming args init fun a line => do
    let mut {last, success, failed, done, speed, pending, currentTask, lastBatchSize, decompressed, decompFailed} := a
    -- output errors other than 404 and remove corresponding partial downloads
    let line := line.trimAscii
    if !line.isEmpty then
      match Lean.Json.parse line.copy with
      | .ok result =>
        match result.getObjValAs? Nat "http_code" with
        | .ok 200
        | .ok 201 =>
          if let .ok fn := result.getObjValAs? String "filename_effective" then
            if (← System.FilePath.pathExists fn) && fn.endsWith ".part" then
              let finalPath := (fn.dropEnd 5).copy
              IO.FS.rename fn finalPath
              -- Add to decompression queue if enabled
              if let some config := decompConfig then
                let some hash := hashFromFileName finalPath | do
                  IO.eprintln s!"Warning: Failed to extract hash from filename: {finalPath}"
                  decompFailed := decompFailed + 1
                let some mod := config.hashToMod[hash]? | do
                  IO.eprintln s!"Warning: No module mapping found for hash {hash} (file: {finalPath})"
                  decompFailed := decompFailed + 1
                pending := pending.push (finalPath, mod)
                -- Check if we should dispatch a batch
                match currentTask with
                | some task =>
                  if (← IO.hasFinished task) then
                    -- Harvest completed task
                    let (d, f, err?) := harvestDecompTask task lastBatchSize decompressed decompFailed
                    decompressed := d
                    decompFailed := f
                    if let some e := err? then
                      IO.eprintln s!"Decompression error: {e}"
                    -- Dispatch new batch with all pending files
                    lastBatchSize := pending.size
                    currentTask ← dispatchDecompBatch pending config
                    pending := #[]
                  -- else: task still running, just accumulate
                | none =>
                  -- No task running, dispatch immediately
                  lastBatchSize := pending.size
                  currentTask ← dispatchDecompBatch pending config
                  pending := #[]
          success := success + 1
        | .ok 404 => pure ()
        | code? =>
          failed := failed + 1
          let mkFailureMsg code? fn? msg? : String := Id.run do
            let mut msg := "Transfer failed"
            if let .ok fn := fn? then
              msg := s!"{fn}: {msg}"
            if let .ok code := code? then
              msg := s!"{msg} (error code: {code})"
            if let .ok errMsg := msg? then
              msg := s!"{msg}: {errMsg}"
            return msg
          let msg? := result.getObjValAs? String "errormsg"
          let fn? :=  result.getObjValAs? String "filename_effective"
          IO.println (mkFailureMsg code? fn? msg?)
          if let .ok fn := fn? then
            if removeOnError then
              -- `curl --remove-on-error` can already do this, but only from 7.83 onwards
              if (← System.FilePath.pathExists fn) then
                IO.FS.removeFile fn
        done := done + 1
        let now ← IO.monoMsNow
        if now - last ≥ 100 then -- max 10/s update rate
          speed := match result.getObjValAs? Nat speedVar with
            | .ok speed => speed | .error _ => speed
          IO.eprint (mkStatus {last, success, failed, done, speed, pending, currentTask, lastBatchSize, decompressed, decompFailed})
          last := now
       | .error e =>
        IO.println s!"Non-JSON output from curl:\n  {line}\n{e}"
    pure {last, success, failed, done, speed, pending, currentTask, lastBatchSize, decompressed, decompFailed}
  if s.done > 0 then
    -- to avoid confusingly moving on without finishing the count
    IO.eprintln (mkStatus s)
  return s

/-- Run one container's download pass for the given hash map. Returns the
`TransferState` produced by `monitorCurl` (or a synthesized empty state in
serial mode). Side effect: any files successfully fetched are written to
`CACHEDIR` with their final names. -/
private def downloadFilesFromContainer
    (container : Option Container) (repo containerURL : String)
    (hashMap : IO.ModuleHashMap)
    (parallel : Bool) (decompConfig : Option DecompConfig) :
    IO (Nat × TransferState) := do
  let size := hashMap.size
  if parallel then
    IO.FS.writeFile IO.CURLCFG (← mkGetConfigContent container repo containerURL hashMap)
    let args := #["--request", "GET", "--parallel",
        -- commented as this creates a big slowdown on curl 8.13.0: "--fail",
        "--silent",
        "--retry", "5", -- there seem to be some intermittent failures
        "--write-out", "%{json}\n", "--config", IO.CURLCFG.toString]
    let s ← monitorCurl args size "Downloaded" "speed_download" (removeOnError := true) decompConfig
    IO.FS.removeFile IO.CURLCFG
    return (s.failed, s)
  else
    let r ← hashMap.foldM (init := []) fun acc _ hash => do
      pure <| (← IO.asTask do downloadFile container repo containerURL hash) :: acc
    let failed := r.foldl (init := 0) fun f t => if let .ok true := t.get then f else f + 1
    let emptyState : TransferState := ⟨0, 0, 0, 0, 0, #[], none, 0, 0, 0⟩
    return (failed, emptyState)

/-- Call `curl` to download files from the server to `CACHEDIR` (`.cache`).
Return the number of files which failed to download.
If `decompress` is true, decompresses files as they're downloaded (pipelined).

For each repo, the tool tries the trust-ordered container list returned by
`effectiveGetURLs`. After each container round, files that were successfully
fetched are filtered out so the next container only retries genuine misses. -/
def downloadFiles
    (repo : String) (hashMap : IO.ModuleHashMap)
    (forceDownload : Bool) (parallel : Bool) (warnOnMissing : Bool)
    (decompress : Bool := false) (forceUnpack : Bool := false)
    (isMathlibRoot : Bool := false) (mathlibDepPath : FilePath := ".") : IO Nat := do
  let hashMap ← if forceDownload then pure hashMap else hashMap.filterExists false
  if hashMap.isEmpty then IO.println "No files to download"; return 0
  let initialSize := hashMap.size
  IO.FS.createDirAll IO.CACHEDIR

  let containerURLs ← effectiveGetURLs repo
  if containerURLs.isEmpty then
    IO.eprintln "No container URLs configured for download"
    return hashMap.size

  -- Set up decompression config if enabled. We keep one config across all
  -- container rounds so pipelined decompression continues across them.
  let decompConfig ← if decompress then
    let hashToMod : Std.HashMap UInt64 Lean.Name := hashMap.fold (init := ∅) fun acc mod hash =>
      acc.insert hash mod
    pure (some { hashToMod, force := forceUnpack, isMathlibRoot, mathlibDepPath : DecompConfig })
  else
    pure none

  -- Walk container URLs in trust order. After each round, drop files that
  -- succeeded so the next round only retries genuine misses.
  let mut remaining := hashMap
  let mut finalState : TransferState := ⟨0, 0, 0, 0, 0, #[], none, 0, 0, 0⟩
  let mut downloadFailed := 0
  let mut roundIdx := 0
  for (container?, url) in containerURLs do
    if remaining.isEmpty then break
    IO.println s!"Attempting to download {remaining.size} file(s) from {repo} cache at {url}"
    let (failed, s) ← downloadFilesFromContainer container? repo url remaining parallel decompConfig
    -- Carry forward the decompression-related state across container rounds.
    -- Counter fields (success/failed/done) reflect only the last round; we
    -- aggregate `downloadFailed` separately below.
    finalState := s
    downloadFailed := failed
    remaining ← remaining.filterExists false
    roundIdx := roundIdx + 1

  if warnOnMissing && downloadFailed > 0 && parallel then
    IO.eprintln "Warning: some files were not found in the cache."
    IO.eprintln "This usually means that your local checkout of mathlib4 has diverged from upstream."
    IO.eprintln ""
    IO.eprintln "  * If you push your commits to a PR to the mathlib4 repository"
    IO.eprintln "    (use a draft PR if it is not ready for review),"
    IO.eprintln "    then CI will build the oleans and they will be available later."
    IO.eprintln "  * If you have already opened a PR, this may mean"
    IO.eprintln "    the CI build has failed part-way through building."
  let _ := initialSize

  -- Finalize decompression: wait for current task and process any remaining files
  if let some config := decompConfig then
    let mut {pending, currentTask, lastBatchSize, decompressed, decompFailed, ..} := finalState

    -- Wait for current task to complete if any
    if let some task := currentTask then
      let (d, f, err?) := harvestDecompTask task lastBatchSize decompressed decompFailed
      decompressed := d
      decompFailed := f
      if let some e := err? then
        IO.eprintln s!"Decompression error: {e}"

    -- Process any remaining pending files
    if !pending.isEmpty then
      try
        decompressBatch pending config.force config.isMathlibRoot config.mathlibDepPath
        decompressed := decompressed + pending.size
      catch e =>
        IO.eprintln s!"Decompression error: {e}"
        decompFailed := decompFailed + pending.size

    IO.println s!"Decompressed {decompressed} file(s)"
    if decompFailed > 0 then
      IO.println s!"{decompFailed} decompression(s) failed"
      IO.Process.exit 1

  if downloadFailed > 0 then
    IO.println s!"{downloadFailed} download(s) failed"
  return downloadFailed

/-- Check if the project's `lean-toolchain` file matches mathlib's.
Print and error and exit the process with error code 1 otherwise. -/
def checkForToolchainMismatch : IO.CacheM Unit := do
  let mathlibToolchainFile := (← read).mathlibDepPath / "lean-toolchain"
  let downstreamToolchain ← IO.FS.readFile "lean-toolchain"
  let mathlibToolchain ← IO.FS.readFile mathlibToolchainFile
  if !(mathlibToolchain.trimAscii == downstreamToolchain.trimAscii) then
    IO.println "Dependency Mathlib uses a different lean-toolchain"
    IO.println s!"  Project uses {downstreamToolchain.trimAscii}"
    IO.println s!"  Mathlib uses {mathlibToolchain.trimAscii}"
    IO.println "\nThe cache will not work unless your project's toolchain matches Mathlib's toolchain"
    IO.println s!"This can be achieved by copying the contents of the file `{mathlibToolchainFile}`
into the `lean-toolchain` file at the root directory of your project"
    if !System.Platform.isWindows then
      IO.println s!"You can use `cp {mathlibToolchainFile} ./lean-toolchain`"
    else
      IO.println s!"On powershell you can use `cp {mathlibToolchainFile} ./lean-toolchain`"
      IO.println s!"On Windows CMD you can use `copy {mathlibToolchainFile} lean-toolchain`"
    IO.Process.exit 1
  return ()

/-- A human-readable description of a manifest package entry's source. -/
def packageEntrySrcDesc (entry : Lake.PackageEntry) : String :=
  match entry.src with
  | .git _ rev _ _ => (rev.take 12).toString
  | .path dir => s!"path:{dir}"

/-- Check whether two manifest package entries refer to the same source. -/
def packageEntrySrcMatch (a b : Lake.PackageEntry) : Bool :=
  match a.src, b.src with
  | .git urlA revA _ subDirA, .git urlB revB _ subDirB =>
    urlA == urlB && revA == revB && subDirA == subDirB
  | .path dirA, .path dirB => dirA == dirB
  | _, _ => false

/-- Check if the project's `lake-manifest.json` pins shared dependencies at different versions
than mathlib's `lake-manifest.json`. Print a warning and exit if so, since the cache will compute
wrong hashes. -/
def checkForManifestMismatch : IO.CacheM Unit := do
  let mathlibDepPath := (← read).mathlibDepPath
  let downstreamEntries ← Lake.Manifest.tryLoadEntries "lake-manifest.json"
  let mathlibEntries ← Lake.Manifest.tryLoadEntries (mathlibDepPath / "lake-manifest.json")
  let downstreamByName : Std.HashMap Lean.Name Lake.PackageEntry :=
    downstreamEntries.foldl (init := ∅) fun m e => m.insert e.name e
  let mut directMismatches : Array (String × String × String) := #[]
  let mut inheritedMismatches : Array (String × String × String) := #[]
  for mathlibEntry in mathlibEntries do
    if let some downstreamEntry := downstreamByName[mathlibEntry.name]? then
      unless packageEntrySrcMatch mathlibEntry downstreamEntry do
        let name := mathlibEntry.name.toString
        let downstreamDesc := packageEntrySrcDesc downstreamEntry
        let mathlibDesc := packageEntrySrcDesc mathlibEntry
        if downstreamEntry.inherited then
          inheritedMismatches := inheritedMismatches.push (name, downstreamDesc, mathlibDesc)
        else
          directMismatches := directMismatches.push (name, downstreamDesc, mathlibDesc)
  let allMismatches := directMismatches ++ inheritedMismatches
  unless allMismatches.isEmpty do
    IO.println "Warning: your project pins different versions of some dependencies than Mathlib."
    IO.println "This will cause `lake exe cache get` to compute wrong hashes.\n"
    for (name, downstreamDesc, mathlibDesc) in allMismatches do
      IO.println s!"  {name}:"
      IO.println s!"    project: {downstreamDesc}"
      IO.println s!"    mathlib: {mathlibDesc}"
    if !directMismatches.isEmpty then
      IO.println "\nRemove these dependencies from your lakefile and let them come \
        transitively from Mathlib."
    if !inheritedMismatches.isEmpty then
      IO.println "\nSome mismatched dependencies come transitively from other packages \
        in your lakefile. \
        Try putting `require mathlib` last in your lakefile so that Mathlib's versions take \
        precedence, then run `lake update`."
    IO.Process.exit 1

/-- Downloads missing files, and unpacks files. -/
def getFiles
    (repo? : Option String) (hashMap : IO.ModuleHashMap)
    (forceDownload forceUnpack parallel decompress : Bool)
    : IO.CacheM Unit := do
  let isMathlibRoot ← IO.isMathlibRoot
  unless isMathlibRoot do
    checkForToolchainMismatch
    checkForManifestMismatch

  let mathlibDepPath := (← read).mathlibDepPath
  let startTime ← IO.monoMsNow

  -- Start background decompression of already-cached files before downloading.
  -- Skip when forceDownload is set, since downloadFiles will re-download (and pipeline-decompress)
  -- all files including already-cached ones, which would race with this background task.
  let bgDecomp ← if decompress && !forceDownload then
    if let some plan := ← IO.prepareDecompConfig hashMap forceUnpack then
      if plan.alreadyDecompressed > 0 then
        IO.println s!"Decompressing {plan.needsDecomp} already-cached file(s) \
          ({plan.alreadyDecompressed} already decompressed)"
      else
        IO.println s!"Decompressing {plan.needsDecomp} already-cached file(s)"
      let task ← IO.asTask (IO.spawnLeanTarDecompress plan.config forceUnpack)
      pure (some (task, plan.needsDecomp))
    else pure none
  else pure none

  -- Resolve the repo once: --repo= override > git remote > MATHLIBREPO.
  -- The trust-ordered container list for this repo (from
  -- `defaultContainersForRepo`) is the single source of truth for what gets
  -- tried — there's no separate outer-loop iteration. Master's cache reaches
  -- fork builds via `master` being in the fork chain (highest-trust source
  -- holding the bulk of any fork's deps).
  let repo ← match repo? with
    | some r => pure r
    | none =>
      match ← getRemoteRepo (← read).mathlibDepPath with
      | some info => pure info.repo
      | none => pure MATHLIBREPO

  let failed ← downloadFiles repo hashMap forceDownload parallel
    (warnOnMissing := true)
    (decompress := decompress) (forceUnpack := forceUnpack)
    isMathlibRoot mathlibDepPath
  if failed > 0 then
    IO.println s!"Downloading {failed} files failed"
    IO.Process.exit 1

  -- Wait for decompression of already-cached files to complete
  if let some (task, size) := bgDecomp then
    match task.get with
    | .ok exitCode =>
      if exitCode != 0 then
        IO.eprintln s!"Decompression of already-cached files failed (exit code {exitCode})"
        IO.Process.exit 1
      IO.println s!"Decompressed {size} already-cached file(s)"
    | .error e =>
      IO.eprintln s!"Decompression of already-cached files error: {e}"
      IO.Process.exit 1

  let elapsed := (← IO.monoMsNow) - startTime
  if decompress then
    if bgDecomp.isSome && parallel then
      -- Background task handled pre-cached files, download pipeline handled new files
      IO.println s!"Completed successfully in {elapsed} ms!"
    else
      -- Either no background decompression ran, or non-parallel mode needs final sweep
      IO.unpackCache hashMap forceUnpack
  else
    IO.println "Downloaded all files successfully!"

end Get

section Put

/--
Resolve the upload base URL.

Precedence:
1. `MATHLIB_CACHE_PUT_URL` env var, if set.
2. The Azure URL for the explicitly chosen `container`.
3. **Migration fallback**: if no `--container` is passed and no env var is
   set, default to `Container.legacy` (the bare `mathlib4` container) with
   a deprecation warning to stderr. This exists so workflow files from
   *before* this PR — which don't pass `--container=NAME` — keep working
   while mathlib4's various branches (bors temp branches, maintainer dev
   branches, the entire nightly-testing repo and its `bump/*`,
   `lean-pr-testing-*`, etc. branches) are absorbing the new workflows.
   Trust model is preserved: legacy is the explicit low-trust catch-all,
   and the RBAC scoping on each identity still prevents low-trust jobs
   from reaching the per-trust-level containers. Once all branches have
   absorbed this PR's workflow files, tighten this back to a hard error.
-/
def effectiveUploadURL (container : Option Container) :
    IO (Option Container × String) := do
  if let some url ← IO.getEnv "MATHLIB_CACHE_PUT_URL" then
    -- Env-var override: we don't know which container's URL-shape policy
    -- applies, so signal that with `none` and let `mkFileURL` fall back to
    -- legacy semantics.
    return (none, url)
  match container with
  | none =>
    IO.eprintln <|
      "Warning: cache upload without --container=NAME; defaulting to the\n" ++
      "         `legacy` (bare `mathlib4`) container. This default is a\n" ++
      "         transitional fallback for workflow files that pre-date the\n" ++
      "         per-trust-level container split. Pass --container=NAME\n" ++
      "         explicitly when you next update this workflow."
    return (some Container.legacy, Container.legacy.azureURL)
  | some c => return (some c, c.azureURL)

def azureBearerApiVersionHeader : String := "x-ms-version: 2026-02-06"

def getAzureDateHeader : IO String := do
  let out ← IO.Process.output
    { cmd := "date", args := #["-u", "+%a, %d %b %Y %H:%M:%S GMT"] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"failed to produce x-ms-date header (exit code {out.exitCode})"
  return s!"x-ms-date: {out.stdout.trimAscii.copy}"

/-- Formats the config file for `curl`, containing the list of files to be uploaded.
The destination base URL is the explicit `uploadURL` argument. `container` is
threaded through to `mkFileURL` so the per-container URL-shape policy applies;
it is `none` only when `MATHLIB_CACHE_PUT_URL` is overriding the endpoint. -/
def mkPutConfigContent (container : Option Container) (repo uploadURL : String)
    (files : Array FilePath) (auth : UploadAuth) : IO String := do
  let scope? ← getRepoScope
  let token := match auth with
    | .azureSas token => s!"?{token}"
    | _ => ""
  let l ← files.toList.mapM fun file : FilePath => do
    pure s!"-T {file.toString}\nurl = {mkFileURL container repo uploadURL file.fileName.get! scope?}{token}"
  return "\n".intercalate l

/-- Calls `curl` to send a set of files to the server. The destination container
is selected by `container`; pass `none` to require `MATHLIB_CACHE_PUT_URL` to
be set instead (otherwise this errors). -/
def putFilesAbsolute
  (repo : String) (container : Option Container)
  (files : Array FilePath) (tempConfigFilePath : FilePath)
  (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let _ := overwrite
  let size := files.size
  if size > 0 then
    let (urlContainer?, uploadURL) ← effectiveUploadURL container
    IO.FS.writeFile tempConfigFilePath
      (← mkPutConfigContent urlContainer? repo uploadURL files auth)
    let target := container.map Container.name |>.getD "(env override)"
    IO.println s!"Attempting to upload {size} file(s) to {repo} cache (container: {target})"
    let azureDateHeader ← getAzureDateHeader
    let args := match auth with
      | .azureSas _ =>
        if overwrite then
          #["-H", "x-ms-blob-type: BlockBlob"]
        else
          #["-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *"]
      | .azureBearer token =>
        if overwrite then
          #["-H", "x-ms-blob-type: BlockBlob", "-H", azureBearerApiVersionHeader, "-H",
            azureDateHeader,
            "--oauth2-bearer", token]
        else
          #["-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *", "-H",
            azureBearerApiVersionHeader, "-H", azureDateHeader, "--oauth2-bearer", token]
    let args := args ++ #[
      "-X", "PUT", "--parallel",
      "--retry", "5", -- there seem to be some intermittent failures
      "--write-out", "%{json}\n", "--config", tempConfigFilePath.toString]
    discard <| monitorCurl args size "Uploaded" "speed_upload" (removeOnError := false) (decompConfig := none)
    IO.FS.removeFile tempConfigFilePath
  else IO.println "No files to upload"

/-- Calls `curl` to send a set of cached files to the server. -/
def putFiles
  (repo : String) (container : Option Container) (fileNames : Array String)
  (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let files : Array FilePath := fileNames.map (fun (f : String) => (IO.CACHEDIR / f))
  putFilesAbsolute repo container files IO.CURLCFG overwrite auth
end Put

section Stage

def copyCmd : String := if System.Platform.isWindows then "COPY" else "cp"

/-- Copies cached files to a directory, intended for 'staging' -/
def stageFiles
    (destinationPath : FilePath) (fileNames : Array String) : IO Unit := do
  let size := fileNames.size
  if size > 0 then
    IO.FS.createDirAll destinationPath
    let paths := fileNames.map (s!"{IO.CACHEDIR / ↑·}")
    let args := paths.push destinationPath.toString
    IO.println s!"Copying {size} file(s) to {destinationPath}"
    discard <| IO.runCmd copyCmd args
  else IO.println "No files to stage"

/-- Copies staged files into the local cache directory. -/
def unstageFiles (stagingDir : FilePath) (overwrite : Bool) : IO Unit := do
  unless (← stagingDir.isDir) do
    IO.println "--staging-dir must be a directory"
    return
  let files ← IO.getFilesWithExtension stagingDir "ltar"
  let enumerationSize := files.size
  IO.println s!"{enumerationSize} files found in staging directory"
  let files ← if overwrite then pure files else
    files.filterM fun file => do
      let dest := IO.CACHEDIR / file.fileName.get!
      return !(← dest.pathExists)
  let size := files.size
  if !overwrite then
    IO.println s!"{enumerationSize -  size} files will be skipped because they exist in the cache"

  if size > 0 then
    IO.FS.createDirAll IO.CACHEDIR
    let args := files.map (·.toString) ++ #[IO.CACHEDIR.toString]
    IO.println s!"Placing {size} file(s) from {stagingDir} into {IO.CACHEDIR}"
    discard <| IO.runCmd copyCmd args
  else
    IO.println "No files to unstage"

end Stage

section Commit

def isGitStatusClean : IO Bool :=
  return (← IO.runCmd "git" #["status", "--porcelain"]).isEmpty

def getGitCommitHash : IO String :=
  return (← IO.runCmd "git" #["rev-parse", "HEAD"]).trimAsciiEnd.copy

/--
Sends a commit file to the server, containing the hashes of the respective committed files.

The file name is the current Git hash and the `c/` prefix means that it's a commit file.
The destination container follows the same rules as `putFiles`.
-/
def commit (container : Option Container) (hashMap : IO.ModuleHashMap) (overwrite : Bool)
    (auth : UploadAuth) : IO Unit := do
  let hash ← getGitCommitHash
  let path := IO.CACHEDIR / hash
  IO.FS.createDirAll IO.CACHEDIR
  IO.FS.writeFile path <| ("\n".intercalate <| hashMap.hashes.toList.map toString) ++ "\n"
  let azureDateHeader ← getAzureDateHeader
  -- Commit files are never namespaced by repo (they always live at `/c/<hash>`),
  -- so we only need the URL from `effectiveUploadURL`, not the URL-shape container.
  let (_, uploadURL) ← effectiveUploadURL container
  match auth with
  | .azureSas token =>
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob"]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *"]
    discard <| IO.runCurl <| params ++ #["-T", path.toString, s!"{uploadURL}/c/{hash}?{token}"]
  | .azureBearer token =>
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", azureBearerApiVersionHeader,
        "-H", azureDateHeader,
        "--oauth2-bearer", token]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *", "-H",
        azureBearerApiVersionHeader, "-H", azureDateHeader, "--oauth2-bearer", token]
    discard <| IO.runCurl <| params ++ #["-T", path.toString, s!"{uploadURL}/c/{hash}"]
  IO.FS.removeFile path

end Commit

section Collect

inductive QueryType
  | files | commits | all

def QueryType.prefix : QueryType → String
  | files   => "&prefix=f/"
  | commits => "&prefix=c/"
  | all     => ""

def formatError {α : Type} : IO α :=
  throw <| IO.userError "Invalid format for curl return"

def QueryType.desc : QueryType → String
  | files   => "hosted files"
  | commits => "hosted commits"
  | all     => "everything"

/--
Retrieves metadata about hosted files: their names and the timestamps of last modification.

Example: `["f/39476538726384726.tar.gz", "Sat, 24 Dec 2022 17:33:01 GMT"]`
-/
def getFilesInfo (q : QueryType) : IO <| List (String × String) := do
  IO.println s!"Downloading info list of {q.desc}"
  let ret ← IO.runCurl
    #["-X", "GET", s!"{masterContainerURL}?comp=list&restype=container{q.prefix}"]
  match ret.splitOn "<Name>" with
  | [] => formatError
  | [_] => return []
  | _ :: parts =>
    parts.mapM fun part => match part.splitOn "</Name>" with
      | [name, rest] => match rest.splitOn "<Last-Modified>" with
        | [_, rest] => match rest.splitOn "</Last-Modified>" with
          | [date, _] => pure (name, date)
          | _ => formatError
        | _ => formatError
      | _ => formatError

end Collect

section Marker

/--
URL for the per-SHA marker blob: `{container}/m/{repo}/{sha}`.

The marker is uploaded by `put-staged` as the last step when an upload is
SHA-scoped (`MATHLIB_CACHE_REPO_SCOPE` set). Its presence at this URL
indicates that the full `.ltar` upload completed for this commit, and lets
`cache query` discover cached commits with a cheap HEAD probe rather than
a blob-listing call.
-/
def markerURL (container : Container) (repo sha : String) : String :=
  s!"{container.azureURL}/m/{repo}/{sha}"

/--
Upload a tiny marker blob to `/m/{repo}/{sha}` in the given container. The
blob content is the SHA itself, as a debugging aid; existence is the
signal.

Called from `put-staged` after the `.ltar` artifact uploads complete. If
this PUT fails the artifacts are already uploaded — the only loss is that
`cache query` will not find this commit — so failures here are logged but
not fatal.
-/
def uploadMarker (container : Container) (repo sha : String) (auth : UploadAuth) :
    IO Unit := do
  let url := markerURL container repo sha
  let path := IO.CACHEDIR / s!"marker-{sha}"
  IO.FS.createDirAll IO.CACHEDIR
  IO.FS.writeFile path s!"{sha}\n"
  let azureDateHeader ← getAzureDateHeader
  try
    match auth with
    | .azureSas token =>
      let params := #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob"]
      discard <| IO.runCurl <| params ++ #["-T", path.toString, s!"{url}?{token}"]
    | .azureBearer token =>
      let params := #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H",
        azureBearerApiVersionHeader, "-H", azureDateHeader, "--oauth2-bearer", token]
      discard <| IO.runCurl <| params ++ #["-T", path.toString, url]
  catch e =>
    IO.eprintln s!"warning: marker upload to {url} failed: {e}"
  IO.FS.removeFile path

end Marker

section Query

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
  let out ← IO.Process.output
    {cmd := (← IO.getCurl),
     args := #["-s", "-o", "/dev/null", "-w", "%{http_code}", "-I", url],
     cwd := "."}
  if out.exitCode != 0 then
    -- Network error; assume no cache at this SHA
    pure false
  else
    pure (out.stdout.trimAscii.toString == "200")

/--
Given a list of SHAs, find the most recent one that has cached entries in the
forks container under the SHA-scoped namespace. Returns the first SHA the probe
accepts, or none if none are found.
-/
def findMostRecentSHAWithCache (shas : List String) (repo : String) :
    IO (Option String) := do
  -- For now, always probe the forks container since that's where SHA scoping applies.
  -- Other containers (master, nightly-testing, pr-toolchain-tests) do not use SHA scoping
  -- in the current implementation.
  let container := Container.forks
  for sha in shas do
    let found ← probeContainerForSHA container repo sha
    if found then
      return (some sha)
  pure none

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

Probes the `forks` container's per-SHA marker, the only SHA-scoped container
today; extend `findMostRecentSHAWithCache` alongside this if SHA scoping is
extended to other containers (Follow-up §6).
-/
def cacheQuerySingle (repo sha : String) : IO Unit := do
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
    IO.println s!"This typically means:"
    IO.println s!"  - CI hasn't built any of these commits yet."
    IO.println s!"  - The commits pre-date the new per-commit cache (rare on recent branches)."

end Query

section Warning

/--
Condition to determine if a non-default scope warning should be printed.

Returns `true` if any of these hold:
1. `MATHLIB_CACHE_REPO_SCOPE` is set in the environment (any non-empty value)
2. `--cache-from` was passed and widens the lookup chain beyond `defaultContainersForRepo` for the resolved repo
3. `--repo` was passed and does not match the cwd's `git remote origin` (or active remote)

Otherwise returns `false` (default lookup chain, no warning needed).
-/
def shouldWarnNonDefaultScope (repoExplicit? : Option String)
    (cliCacheFromOverride? : Option (List Container)) (resolvedRepo : String) :
    IO Bool := do
  -- Condition 1: `--scope=` flag or `MATHLIB_CACHE_REPO_SCOPE` env var supplied
  if (← getRepoScope).isSome then return true

  -- Condition 2: --cache-from CLI override widens the lookup chain
  match cliCacheFromOverride? with
  | some cliOverride =>
    let defaultContainers := defaultContainersForRepo resolvedRepo
    unless cliOverride == defaultContainers do
      return true
  | none => pure ()

  -- Condition 3: --repo was explicitly passed AND does not match cwd's git remote.
  -- Only fires when the user explicitly overrode --repo; defaulting to MATHLIBREPO
  -- from a fork checkout is normal and does not warn.
  match repoExplicit? with
  | some explicitRepo =>
    let curRemoteRepo? ← getRemoteRepo "."
    match curRemoteRepo? with
    | some repoInfo =>
      unless explicitRepo == repoInfo.repo do
        return true
    | none =>
      -- Can't determine current repo; don't warn
      pure ()
  | none => pure ()

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
def getNonDefaultScopeReason (repoExplicit? : Option String)
    (cliCacheFromOverride? : Option (List Container)) (resolvedRepo : String) :
    IO String := do
  -- Check conditions in order; return the first that matches.

  -- Condition 1: `--scope=` flag (preferred form) or `MATHLIB_CACHE_REPO_SCOPE`
  -- env var (CI form). Reported with the source that set it.
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
    if cliOverride ≠ defaultContainers then
      let overrideStr := ", ".intercalate (cliOverride.map Container.name)
      return s!"--cache-from={overrideStr} (explicit container override)"

  -- Condition 3: --repo was explicitly passed AND doesn't match cwd's git remote
  match repoExplicit? with
  | some explicitRepo =>
    let curRemoteRepo? ← getRemoteRepo "."
    match curRemoteRepo? with
    | some repoInfo =>
      if explicitRepo ≠ repoInfo.repo then
        return s!"--repo={explicitRepo} (overrides detected git remote: {repoInfo.repo})"
    | none => pure ()
  | none => pure ()

  return "unknown reason"

/--
Check if a non-default scope warning should be printed and issue it if so.

This is called before performing read operations (cache get). It checks
the three conditions and prints the warning if any hold, but does not
prompt for confirmation (so as not to break CI).
-/
def warnIfNonDefaultScope (repoExplicit? : Option String)
    (cliCacheFromOverride? : Option (List Container)) (resolvedRepo : String) :
    IO Unit := do
  if (← shouldWarnNonDefaultScope repoExplicit? cliCacheFromOverride? resolvedRepo) then
    let reason ← getNonDefaultScopeReason repoExplicit? cliCacheFromOverride? resolvedRepo
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

One HEAD probe per invocation; the message is stderr-only so it doesn't
mix with `cache get`'s stdout output.
-/
def informIfHeadNotBuilt (repoExplicit? : Option String) : IO Unit := do
  if (← getRepoScope).isSome then return
  if (← cacheFromOverride.get).isSome then return
  -- Resolve repo: --repo= flag wins; otherwise use the git remote (same as
  -- `getFiles` does when no --repo is passed). Skip silently if neither
  -- yields, since we have nowhere to probe.
  let repo ← match repoExplicit? with
    | some r => pure r
    | none =>
      match ← getRemoteRepo "." with
      | some info => pure info.repo
      | none => return
  unless (defaultContainersForRepo repo).contains Container.forks do return
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

end Warning

end Cache.Requests
