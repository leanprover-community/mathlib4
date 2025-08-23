/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Batteries.Data.String.Matcher
import Cache.Hashing

namespace Cache.Requests

open System (FilePath)

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
  let url := url.stripSuffix ".git"
  let pos ← url.revFind (· == '/')
  let pos ← url.revFindAux (fun c => c == '/'  || c == ':') pos
  return url.extract (url.next pos) url.endPos

/-- Spot check if a URL is valid for a git remote -/
def isRemoteURL (url : String) : Bool :=
  "https://".isPrefixOf url || "http://".isPrefixOf url || "git@github.com:".isPrefixOf url

/--
Helper function to get repository from a remote name
-/
def getRepoFromRemote (mathlibDepPath : FilePath) (remoteName : String) (errorContext : String) : IO String := do
  -- If the remote is already a valid URL, attempt to extract the repo from it. This happens with `gh pr checkout`
  if isRemoteURL remoteName then
    repoFromURL remoteName
  else
  -- If not, we use `git remote get-url` to find the URL of the remote. This assumes the remote has a
  -- standard name like `origin` or `upstream` or it errors out.
  let out ← IO.Process.output
    {cmd := "git", args := #["remote", "get-url", remoteName], cwd := mathlibDepPath}
  -- If `git remote get-url` fails then bail out with an error to help debug
  let output := out.stdout.trim
  unless out.exitCode == 0 do
    throw <| IO.userError s!"\
      Failed to run Git to determine Mathlib's repository from {remoteName} remote (exit code: {out.exitCode}).\n\
      {errorContext}\n\
      Stdout:\n{output}\nStderr:\n{out.stderr.trim}\n"
  -- Finally attempt to extract the repository from the remote URL returned by `git remote get-url`
  repoFromURL output
where repoFromURL (url : String) : IO String := do
    if let some repo := extractRepoFromUrl url then
      return repo
    else
      throw <| IO.userError s!"\
        Failed to extract repository from remote URL: {url}.\n\
        {errorContext}\n\
        Please ensure the remote URL is valid and points to a GitHub repository."

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
      Stdout:\n{remotesInfo.stdout.trim}\nStderr:\n{remotesInfo.stderr.trim}\n"

  let remoteLines := remotesInfo.stdout.split (· == '\n')
  let mut mathlibRemote : Option String := none
  let mut originPointsToMathlib : Bool := false

  for line in remoteLines do
    let parts := line.trim.split (· == '\t')
    if parts.length >= 2 then
      let remoteName := parts[0]!
      let remoteUrl := parts[1]!.takeWhile (· != ' ') -- Remove (fetch) or (push) suffix

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
  let parts := ref.split (· == '/')
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
    let commitHash := currentCommit.stdout.trim
    let tagInfo ← IO.Process.output
      {cmd := "git", args := #["name-rev", "--tags", commitHash], cwd := mathlibDepPath}
    if tagInfo.exitCode == 0 then
      let parts := tagInfo.stdout.trim.splitOn " "
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
def getRemoteRepo (mathlibDepPath : FilePath) : IO RepoInfo := do

  -- Since currently we need to push a PR to `leanprover-community/mathlib` build a user cache,
  -- we check if we are a special branch or a branch with PR. This leaves out non-PRed fork
  -- branches. These should be covered if we ever change how the cache is uploaded from forks
  -- to obviate the need for a PR.
  let currentBranch ← IO.Process.output
    {cmd := "git", args := #["rev-parse", "--abbrev-ref", "HEAD"], cwd := mathlibDepPath}

  if currentBranch.exitCode == 0 then
    let branchName := currentBranch.stdout.trim.stripPrefix "heads/"
    IO.println s!"Current branch: {branchName}"

    -- Check if we're in a detached HEAD state at a nightly-testing tag
    let isDetachedAtNightlyTesting ← if branchName == "HEAD" then
      isDetachedAtNightlyTesting mathlibDepPath
    else
      pure false

    -- Check if we're on a branch that should use nightly-testing remote
    let shouldUseNightlyTesting := branchName == "nightly-testing" ||
                                  branchName.startsWith "lean-pr-testing-" ||
                                  branchName.startsWith "batteries-pr-testing-" ||
                                  branchName.startsWith "bump/" ||
                                  isDetachedAtNightlyTesting

    if shouldUseNightlyTesting then
      -- Try to use nightly-testing remote
      let repo ← getRepoFromRemote mathlibDepPath "nightly-testing"
        s!"Branch '{branchName}' should use the nightly-testing remote, but it's not configured.\n\
          Please add the nightly-testing remote pointing to the nightly testing repository:\n\
          git remote add nightly-testing https://github.com/leanprover-community/mathlib4-nightly-testing.git"
      IO.println s!"Using cache from nightly-testing remote: {repo}"
      return {repo := repo, useFirst := true}

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
    {cmd := "git", args := #["config", "--get", s!"branch.{currentBranch.stdout.trim}.remote"], cwd := mathlibDepPath}

  let remoteName := if trackingRemote.exitCode == 0 then
    trackingRemote.stdout.trim
  else
    -- If no tracking remote is configured, fall back to origin
    "origin"

  let repo ← getRepoFromRemote mathlibDepPath remoteName
    s!"Ensure Git is installed and the '{remoteName}' remote points to its GitHub repository."
  IO.println s!"Using cache from {remoteName}: {repo}"
  return {repo := repo, useFirst := false}

-- FRO cache may be flaky: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/The.20cache.20doesn't.20work/near/411058849
def useFROCache : Bool := true

/-- Public URL for mathlib cache -/
def URL : String :=
  if useFROCache then
    "https://mathlib4.lean-cache.cloud"
  else
    "https://lakecache.blob.core.windows.net/mathlib4"

/-- Retrieves the azure token from the environment -/
def getToken : IO String := do
  let envVar := if useFROCache then "MATHLIB_CACHE_S3_TOKEN" else "MATHLIB_CACHE_SAS"
  let some token ← IO.getEnv envVar
    | throw <| IO.userError s!"environment variable {envVar} must be set to upload caches"
  return token

/-- The full name of the main Mathlib GitHub repository. -/
def MATHLIBREPO := "leanprover-community/mathlib4"

/--
Given a file name like `"1234.tar.gz"`, makes the URL to that file on the server.

The `f/` prefix means that it's a common file for caching.
-/
def mkFileURL (repo URL fileName : String) : String :=
  let pre := if !useFROCache && repo == MATHLIBREPO then "" else s!"{repo}/"
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

/-- Call `curl` to download files from the server to `CACHEDIR` (`.cache`).
Exit the process with exit code 1 if any files failed to download. -/
def downloadFiles
    (repo : String) (hashMap : IO.ModuleHashMap)
    (forceDownload : Bool) (parallel : Bool) (warnOnMissing : Bool): IO Unit := do
  let hashMap ← if forceDownload then pure hashMap else hashMap.filterExists false
  let size := hashMap.size
  if size > 0 then
    IO.FS.createDirAll IO.CACHEDIR
    IO.println s!"Attempting to download {size} file(s) from {repo} cache"
    let failed ← if parallel then
      IO.FS.writeFile IO.CURLCFG (← mkGetConfigContent repo hashMap)
      let args := #["--request", "GET", "--parallel",
          -- commented as this creates a big slowdown on curl 8.13.0: "--fail",
          "--silent",
          "--retry", "5", -- there seem to be some intermittent failures
          "--write-out", "%{json}\n", "--config", IO.CURLCFG.toString]
      let (_, success, failed, done) ←
          IO.runCurlStreaming args (← IO.monoMsNow, 0, 0, 0) fun a line => do
        let mut (last, success, failed, done) := a
        -- output errors other than 404 and remove corresponding partial downloads
        let line := line.trim
        if !line.isEmpty then
          let result ← IO.ofExcept <| Lean.Json.parse line
          match result.getObjValAs? Nat "http_code" with
          | .ok 200 =>
            if let .ok fn := result.getObjValAs? String "filename_effective" then
              if (← System.FilePath.pathExists fn) && fn.endsWith ".part" then
                IO.FS.rename fn (fn.dropRight 5)
            success := success + 1
          | .ok 404 => pure ()
          | _ =>
            failed := failed + 1
            if let .ok e := result.getObjValAs? String "errormsg" then
              IO.println e
            -- `curl --remove-on-error` can already do this, but only from 7.83 onwards
            if let .ok fn := result.getObjValAs? String "filename_effective" then
              if (← System.FilePath.pathExists fn) then
                IO.FS.removeFile fn
          done := done + 1
          let now ← IO.monoMsNow
          if now - last ≥ 100 then -- max 10/s update rate
            let mut msg := s!"\rDownloaded: {success} file(s) [attempted {done}/{size} = {100*done/size}%]"
            if failed != 0 then
              msg := msg ++ s!", {failed} failed"
            IO.eprint msg
            last := now
        pure (last, success, failed, done)
      if done > 0 then
        -- to avoid confusingly moving on without finishing the count
        let mut msg := s!"\rDownloaded: {success} file(s) [attempted {done}/{size} = {100*done/size}%] ({100*success/done}% success)"
        if failed != 0 then
          msg := msg ++ s!", {failed} failed"
        IO.eprintln msg
      IO.FS.removeFile IO.CURLCFG
      if warnOnMissing && success + failed < done then
        IO.eprintln "Warning: some files were not found in the cache."
        IO.eprintln "This usually means that your local checkout of mathlib4 has diverged from upstream."
        IO.eprintln "If you push your commits to a branch of the mathlib4 repository, CI will build the oleans and they will be available later."
        IO.eprintln "Alternatively, if you already have pushed your commits to a branch, this may mean the CI build has failed part-way through building."
        IO.eprintln "During August 2025, we are changing the back-end for the olean cache. If you are unexpectedly not finding oleans for your PR, please try merging `master`."
      pure failed
    else
      let r ← hashMap.foldM (init := []) fun acc _ hash => do
        pure <| (← IO.asTask do downloadFile repo hash) :: acc
      pure <| r.foldl (init := 0) fun f t => if let .ok true := t.get then f else f + 1
    if failed > 0 then
      IO.println s!"{failed} download(s) failed"
      IO.Process.exit 1
  else IO.println "No files to download"

/-- Check if the project's `lean-toolchain` file matches mathlib's.
Print and error and exit the process with error code 1 otherwise. -/
def checkForToolchainMismatch : IO.CacheM Unit := do
  let mathlibToolchainFile := (← read).mathlibDepPath / "lean-toolchain"
  let downstreamToolchain ← IO.FS.readFile "lean-toolchain"
  let mathlibToolchain ← IO.FS.readFile mathlibToolchainFile
  if !(mathlibToolchain.trim = downstreamToolchain.trim) then
    IO.println "Dependency Mathlib uses a different lean-toolchain"
    IO.println s!"  Project uses {downstreamToolchain.trim}"
    IO.println s!"  Mathlib uses {mathlibToolchain.trim}"
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

/-- Fetches the ProofWidgets cloud release and prunes non-JS files. -/
def getProofWidgets (buildDir : FilePath) : IO Unit := do
  if (← buildDir.pathExists) then
    -- Check if the ProofWidgets build is out-of-date via `lake`.
    -- This is done through Lake as cache has no simple heuristic
    -- to determine whether the ProofWidgets JS is out-of-date.
    let exitCode ← (← IO.Process.spawn {cmd := "lake", args := #["-q", "build", "--no-build", "proofwidgets:release"]}).wait
    if exitCode == 0 then -- up-to-date
      return
    else if exitCode == 3 then -- needs fetch (`--no-build` triggered)
      pure ()
    else
      throw <| IO.userError s!"Failed to validate ProofWidgets cloud release: lake failed with error code {exitCode}"
  -- Download and unpack the ProofWidgets cloud release (for its `.js` files)
  let exitCode ← (← IO.Process.spawn {cmd := "lake", args := #["-q", "build", "proofwidgets:release"]}).wait
  if exitCode != 0 then
    throw <| IO.userError s!"Failed to fetch ProofWidgets cloud release: lake failed with error code {exitCode}"
  -- Prune non-JS ProofWidgets files (e.g., `olean`, `.c`)
  try
    IO.FS.removeDirAll (buildDir / "lib")
    IO.FS.removeDirAll (buildDir / "ir")
  catch e =>
    throw <| IO.userError s!"Failed to prune ProofWidgets cloud release: {e}"

/-- Downloads missing files, and unpacks files. -/
def getFiles
    (repo? : Option String) (hashMap : IO.ModuleHashMap)
    (forceDownload forceUnpack parallel decompress : Bool)
    : IO.CacheM Unit := do
  let isMathlibRoot ← IO.isMathlibRoot
  unless isMathlibRoot do checkForToolchainMismatch
  getProofWidgets (← read).proofWidgetsBuildDir

  if let some repo := repo? then
    downloadFiles repo hashMap forceDownload parallel (warnOnMissing := true)
  else
    let repoInfo ← getRemoteRepo (← read).mathlibDepPath

    -- Build list of repositories to download from in order
    let repos : List String :=
      if repoInfo.repo == MATHLIBREPO then
        [repoInfo.repo]
      else if repoInfo.useFirst then
        [repoInfo.repo, MATHLIBREPO]
      else
        [MATHLIBREPO, repoInfo.repo]

    for h : i in [0:repos.length] do
      downloadFiles repos[i] hashMap forceDownload parallel (warnOnMissing := i = repos.length - 1)

  if decompress then
    IO.unpackCache hashMap forceUnpack
  else
    IO.println "Downloaded all files successfully!"

end Get

section Put

/-- FRO cache S3 URL -/
def UPLOAD_URL : String :=
  if useFROCache then
    "https://a09a7664adc082e00f294ac190827820.r2.cloudflarestorage.com/mathlib4"
  else
    URL

/-- Formats the config file for `curl`, containing the list of files to be uploaded -/
def mkPutConfigContent (repo : String) (fileNames : Array String) (token : String) : IO String := do
  let token := if useFROCache then "" else s!"?{token}" -- the FRO cache doesn't pass the token here
  let l ← fileNames.toList.mapM fun fileName : String => do
    pure s!"-T {(IO.CACHEDIR / fileName).toString}\nurl = {mkFileURL repo UPLOAD_URL fileName}{token}"
  return "\n".intercalate l

/-- Calls `curl` to send a set of cached files to the server -/
def putFiles
  (repo : String) (fileNames : Array String)
  (overwrite : Bool) (token : String) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let _ := overwrite
  let size := fileNames.size
  if size > 0 then
    IO.FS.writeFile IO.CURLCFG (← mkPutConfigContent repo fileNames token)
    IO.println s!"Attempting to upload {size} file(s) to {repo} cache"
    let args := if useFROCache then
      -- TODO: reimplement using HEAD requests?
      let _ := overwrite
      #["--aws-sigv4", "aws:amz:auto:s3", "--user", token]
    else if overwrite then
      #["-H", "x-ms-blob-type: BlockBlob"]
    else
      #["-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *"]
    let out ← IO.runCurl (stderrAsErr := false) (args ++ #[
      "--retry", "5", -- there seem to be some intermittent failures
      "-X", "PUT", "--parallel", "-K", IO.CURLCFG.toString])
    if out.trim != "" then
      IO.println s!"Output from curl:"
      IO.println out
    IO.FS.removeFile IO.CURLCFG
  else IO.println "No files to upload"

end Put

section Commit

def isGitStatusClean : IO Bool :=
  return (← IO.runCmd "git" #["status", "--porcelain"]).isEmpty

def getGitCommitHash : IO String := return (← IO.runCmd "git" #["rev-parse", "HEAD"]).trimRight

/--
Sends a commit file to the server, containing the hashes of the respective committed files.

The file name is the current Git hash and the `c/` prefix means that it's a commit file.
-/
def commit (hashMap : IO.ModuleHashMap) (overwrite : Bool) (token : String) : IO Unit := do
  let hash ← getGitCommitHash
  let path := IO.CACHEDIR / hash
  IO.FS.createDirAll IO.CACHEDIR
  IO.FS.writeFile path <| ("\n".intercalate <| hashMap.hashes.toList.map toString) ++ "\n"
  if useFROCache then
    -- TODO: reimplement using HEAD requests?
    let _ := overwrite
    discard <| IO.runCurl #["-T", path.toString,
      "--aws-sigv4", "aws:amz:auto:s3", "--user", token, s!"{UPLOAD_URL}/c/{hash}"]
  else
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob"]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *"]
    discard <| IO.runCurl <| params ++ #["-T", path.toString, s!"{URL}/c/{hash}?{token}"]
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
  if useFROCache then
    throw <| .userError "FIXME: getFilesInfo is not adapted to FRO cache yet"
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
