/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Batteries.Data.String.Matcher
import Cache.Hashing
import Cache.Init
import Lake.Load.Manifest

namespace Cache.Requests

open System (FilePath)

/-- The full name of the main Mathlib GitHub repository. -/
def MATHLIBREPO := "leanprover-community/mathlib4"

/--
Structure to hold repository information with priority ordering
-/
structure RepoInfo where
  repo : String
  useFirst : Bool
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
      let isMathlibRepo := remoteUrl.containsSubstr "leanprover-community/mathlib4"

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
      let cacheService := if useCloudflareCache then "Cloudflare" else "Azure"
      IO.println s!"Using cache ({cacheService}) from nightly-testing remote: {repo}"
      return some {repo := repo, useFirst := true}

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
  let cacheService := if useCloudflareCache then "Cloudflare" else "Azure"
  match repo? with
  | some repo =>
    IO.println s!"Using cache ({cacheService}) from {remoteName}: {repo?}"
    return some {repo := repo, useFirst := false}
  | none =>
    IO.println s!"Using cache ({cacheService}) from {MATHLIBREPO}."
    return none

/-- Public URL for mathlib cache -/
initialize URL : String ← do
  let url? ← IO.getEnv "MATHLIB_CACHE_GET_URL"
  let defaultUrl :=
    if useCloudflareCache then
      "https://mathlib4.lean-cache.cloud"
    else
      "https://lakecache.blob.core.windows.net/mathlib4"
  return url?.getD defaultUrl

/-- Authentication method used for cache upload operations. -/
inductive UploadAuth where
  | cloudflareS3 (token : String)
  | azureSas (token : String)
  | azureBearer (token : String)

/-- Retrieves upload credentials from the environment. -/
def getUploadAuth : IO UploadAuth := do
  if useCloudflareCache then
    let envVar := "MATHLIB_CACHE_S3_TOKEN"
    let some token ← IO.getEnv envVar
      | throw <| IO.userError s!"environment variable {envVar} must be set to upload caches"
    return .cloudflareS3 token
  else
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
Given a file name like `"1234.tar.gz"`, makes the URL to that file on the server.

The `f/` prefix means that it's a common file for caching.
-/
def mkFileURL (repo URL fileName : String) : String :=
  let pre := if !useCloudflareCache && repo == MATHLIBREPO then "" else s!"{repo}/"
  s!"{URL}/f/{pre}{fileName}"

section Get

/-- Formats the config file for `curl`, containing the list of files to be downloaded -/
def mkGetConfigContent (repo : String) (hashMap : IO.ModuleHashMap) : IO String := do
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
    pure <| acc ++ s!"url = {mkFileURL repo URL fileName}\n\
      -o {(IO.CACHEDIR / (fileName ++ ".part")).toString.quote}\n"

/-- Calls `curl` to download a single file from the server to `CACHEDIR` (`.cache`) -/
def downloadFile (repo : String) (hash : UInt64) : IO Bool := do
  let fileName := hash.asLTar
  let url := mkFileURL repo URL fileName
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

/-- Call `curl` to download files from the server to `CACHEDIR` (`.cache`).
Return the number of files which failed to download.
If `decompress` is true, decompresses files as they're downloaded (pipelined). -/
def downloadFiles
    (repo : String) (hashMap : IO.ModuleHashMap)
    (forceDownload : Bool) (parallel : Bool) (warnOnMissing : Bool)
    (decompress : Bool := false) (forceUnpack : Bool := false)
    (isMathlibRoot : Bool := false) (mathlibDepPath : FilePath := ".") : IO Nat := do
  let hashMap ← if forceDownload then pure hashMap else hashMap.filterExists false
  if hashMap.isEmpty then IO.println "No files to download"; return 0
  let size := hashMap.size
  IO.FS.createDirAll IO.CACHEDIR
  IO.println s!"Attempting to download {size} file(s) from {repo} cache"

  -- Set up decompression config if enabled
  let decompConfig ← if decompress then
    -- Build hash → module name mapping
    let hashToMod : Std.HashMap UInt64 Lean.Name := hashMap.fold (init := ∅) fun acc mod hash =>
      acc.insert hash mod
    pure (some { hashToMod, force := forceUnpack, isMathlibRoot, mathlibDepPath : DecompConfig })
  else
    pure none

  let (downloadFailed, finalState) ← if parallel then
    IO.FS.writeFile IO.CURLCFG (← mkGetConfigContent repo hashMap)
    let args := #["--request", "GET", "--parallel",
        -- commented as this creates a big slowdown on curl 8.13.0: "--fail",
        "--silent",
        "--retry", "5", -- there seem to be some intermittent failures
        "--write-out", "%{json}\n", "--config", IO.CURLCFG.toString]
    let s ← monitorCurl args size "Downloaded" "speed_download" (removeOnError := true) decompConfig
    IO.FS.removeFile IO.CURLCFG
    if warnOnMissing && s.success + s.failed < s.done then
      IO.eprintln "Warning: some files were not found in the cache."
      IO.eprintln "This usually means that your local checkout of mathlib4 has diverged from upstream."
      IO.eprintln ""
      IO.eprintln "  * If you push your commits to a PR to the mathlib4 repository"
      IO.eprintln "    (use a draft PR if it is not ready for review),"
      IO.eprintln "    then CI will build the oleans and they will be available later."
      IO.eprintln "  * If you have already opened a PR, this may mean"
      IO.eprintln "    the CI build has failed part-way through building."
    pure (s.failed, s)
  else
    let r ← hashMap.foldM (init := []) fun acc _ hash => do
      pure <| (← IO.asTask do downloadFile repo hash) :: acc
    let failed := r.foldl (init := 0) fun f t => if let .ok true := t.get then f else f + 1
    -- Non-parallel mode doesn't support pipelined decompression
    let emptyState : TransferState := ⟨0, 0, 0, 0, 0, #[], none, 0, 0, 0⟩
    pure (failed, emptyState)

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

  if let some repo := repo? then
    let failed ← downloadFiles repo hashMap forceDownload parallel (warnOnMissing := true)
      (decompress := decompress) (forceUnpack := forceUnpack)
      isMathlibRoot mathlibDepPath
    if failed > 0 then IO.Process.exit 1
  else
    let repoInfo? ← getRemoteRepo (← read).mathlibDepPath

    -- Build list of repositories to download from in order
    let repos : List String :=
      if let some repoInfo := repoInfo? then
        if repoInfo.repo == MATHLIBREPO then
          [MATHLIBREPO]
        else if repoInfo.useFirst then
          [repoInfo.repo, MATHLIBREPO]
        else
          [MATHLIBREPO, repoInfo.repo]
      else
        [MATHLIBREPO]

    let mut failed : Nat := 0
    for h : i in [0:repos.length] do
      failed := ← downloadFiles repos[i] hashMap forceDownload parallel
        (warnOnMissing := i = repos.length - 1)
        (decompress := decompress) (forceUnpack := forceUnpack)
        isMathlibRoot mathlibDepPath
      if failed > 10 then
        IO.println s!"Too many downloads failed; stopping the downloading"
        IO.Process.exit 1
    if failed > 0 then
      IO.println s!"Downloading {failed} files failed"
      IO.Process.exit 1

  if decompress then
    -- decompress anything which hasn't already been decompressed during download
    IO.unpackCache hashMap forceUnpack
  else
    IO.println "Downloaded all files successfully!"

end Get

section Put

/-- Cloudflare cache S3 URL -/
initialize UPLOAD_URL : String ← do
  let url? ← IO.getEnv "MATHLIB_CACHE_PUT_URL"
  let defaultUrl :=
    if useCloudflareCache then
      "https://a09a7664adc082e00f294ac190827820.r2.cloudflarestorage.com/mathlib4"
    else
      "https://lakecache.blob.core.windows.net/mathlib4"
  return url?.getD defaultUrl

def azureBearerApiVersionHeader : String := "x-ms-version: 2026-02-06"

def getAzureDateHeader : IO String := do
  let out ← IO.Process.output
    { cmd := "date", args := #["-u", "+%a, %d %b %Y %H:%M:%S GMT"] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"failed to produce x-ms-date header (exit code {out.exitCode})"
  return s!"x-ms-date: {out.stdout.trimAscii.copy}"

/-- Formats the config file for `curl`, containing the list of files to be uploaded -/
def mkPutConfigContent (repo : String) (files : Array FilePath) (auth : UploadAuth) : IO String := do
  let token := match auth with
    | .azureSas token => s!"?{token}"
    | _ => ""
  let l ← files.toList.mapM fun file : FilePath => do
    pure s!"-T {file.toString}\nurl = {mkFileURL repo UPLOAD_URL file.fileName.get!}{token}"
  return "\n".intercalate l

/-- Calls `curl` to send a set of files to the server -/
def putFilesAbsolute
  (repo : String) (files : Array FilePath) (tempConfigFilePath : FilePath)
  (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let _ := overwrite
  let size := files.size
  if size > 0 then
    IO.FS.writeFile tempConfigFilePath (← mkPutConfigContent repo files auth)
    IO.println s!"Attempting to upload {size} file(s) to {repo} cache"
    let azureDateHeader ← getAzureDateHeader
    let args := match auth with
      | .cloudflareS3 token =>
        -- TODO: reimplement using HEAD requests?
        let _ := overwrite
        #["--aws-sigv4", "aws:amz:auto:s3", "--user", token]
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

/-- Calls `curl` to send a set of cached files to the server -/
def putFiles
  (repo : String) (fileNames : Array String)
  (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let files : Array FilePath := fileNames.map (fun (f : String) => (IO.CACHEDIR / f))
  putFilesAbsolute repo files IO.CURLCFG overwrite auth
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
-/
def commit (hashMap : IO.ModuleHashMap) (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  let hash ← getGitCommitHash
  let path := IO.CACHEDIR / hash
  IO.FS.createDirAll IO.CACHEDIR
  IO.FS.writeFile path <| ("\n".intercalate <| hashMap.hashes.toList.map toString) ++ "\n"
  let azureDateHeader ← getAzureDateHeader
  match auth with
  | .cloudflareS3 token =>
    -- TODO: reimplement using HEAD requests?
    let _ := overwrite
    discard <| IO.runCurl #["-T", path.toString,
      "--aws-sigv4", "aws:amz:auto:s3", "--user", token, s!"{UPLOAD_URL}/c/{hash}"]
  | .azureSas token =>
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob"]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *"]
    discard <| IO.runCurl <| params ++ #["-T", path.toString, s!"{URL}/c/{hash}?{token}"]
  | .azureBearer token =>
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", azureBearerApiVersionHeader,
        "-H", azureDateHeader,
        "--oauth2-bearer", token]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *", "-H",
        azureBearerApiVersionHeader, "-H", azureDateHeader, "--oauth2-bearer", token]
    discard <| IO.runCurl <| params ++ #["-T", path.toString, s!"{URL}/c/{hash}"]
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
  if useCloudflareCache then
    throw <| .userError "FIXME: getFilesInfo is not adapted to Cloudflare cache yet"
  IO.println s!"Downloading info list of {q.desc}"
  let ret ← IO.runCurl #["-X", "GET", s!"{URL}?comp=list&restype=container{q.prefix}"]
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

end Cache.Requests
