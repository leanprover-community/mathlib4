/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.Hashing

namespace Cache.Requests

open System (FilePath)

/--
Attempts to determine the GitHub repository of a version of Mathlib from its `origin` Git remote.
-/
def getRemoteRepo (mathlibDepPath : FilePath) : IO String := do
  let out ← IO.Process.output
    {cmd := "git", args := #["remote", "get-url", "origin"], cwd := mathlibDepPath}
  unless out.exitCode == 0 do
    throw <| IO.userError s!"\
      Failed to run Git to determine Mathlib's repository (exit code: {out.exitCode}).\n\
      Ensure Git is installed and Mathlib's `origin` remote points to its GitHub repository.\n\
      Stdout:\n{out.stdout.trim}\nStderr:\n{out.stderr.trim}\n"
  -- No strong validation is done here because this is simply used as a smart default
  -- for `lake exe cache get`, which is freely modifiable by any user.
  let url := out.stdout.trim.stripSuffix ".git"
  let repo? : Option String := do
    let pos ← url.revFind (· == '/')
    let pos ← url.revFindAux (fun c => c == '/'  || c == ':') pos
    return url.extract (url.next pos) url.endPos
  if let some repo := repo? then
    return repo
  else
    throw <| IO.userError s!"\
      Failed to determine Mathlib's repository from its remote URL.\n\
      Ensure Mathlib's `origin` Git remote points to its GitHub repository.\n\
      Detected URL: {url}"

-- FRO cache is flaky so disable until we work out the kinks: https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/The.20cache.20doesn't.20work/near/411058849
def useFROCache : Bool := false

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
  let pre := if repo == MATHLIBREPO then "" else s!"{repo}/"
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
      let args := #["--request", "GET", "--parallel", "--fail", "--silent",
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
    let repo ← getRemoteRepo (← read).mathlibDepPath
    IO.println s!"Mathlib repository: {repo}"
    unless repo == MATHLIBREPO do
      downloadFiles MATHLIBREPO hashMap forceDownload parallel (warnOnMissing := false)
    downloadFiles repo hashMap forceDownload parallel (warnOnMissing := true)
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
    _ ← IO.runCurl (stderrAsErr := false) (args ++ #[
      "--retry", "5", -- there seem to be some intermittent failures
      "-X", "PUT", "--parallel", "-K", IO.CURLCFG.toString])
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
