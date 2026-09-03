/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Marcelo Lynch
-/

import Cache.Hashing
import Cache.Infra
import Lake.Load.Manifest

/-!
# Cache transfers

The shared read mechanism under every workflow (`Cache.Workflow`): the URL
contract of a file (`mkFileURL`), the `curl` transfer and its classification,
the decompression pipeline, and the download rounds (`downloadFiles`,
`getFiles`). It also holds the staging commands. Which rounds a read takes is
the workflow's decision, not this module's.
-/

namespace Cache.Requests

open System (FilePath)

/--
`curl` flags that let a cache read follow a redirect, so a read base may answer
with the blob's current home. `%{http_code}` reports the final response, so a
hit reads as a hit and a miss as a miss.

A redirect may target only `https`, and the chain is short. These bounds limit
the transport rather than the trust: the host that answers a read serves the
artifact bytes in either case. They keep a redirect from moving a transfer to a
plaintext protocol or through a long chain of hops.
-/
def curlFollowRedirectArgs : Array String :=
  #["--location", "--proto-redir", "=https", "--max-redirs", "5"]

/--
`curl` retry flags for a cache transfer. `--retry` covers timeouts and
408/429/5xx; every supported curl accepts it. With
`supportLegacyCurl := false`, `--retry-all-errors` also retries transport
errors on a fresh connection, with exponential backoff. That flag needs
curl 7.71; `validateCurl` gates parallel mode at 7.75, which also
guarantees the per-transfer JSON report fields `monitorCurl` reads. Pass
`supportLegacyCurl := true` on paths that must work on older curls.
-/
def curlRetryArgs (supportLegacyCurl : Bool) : Array String :=
  #["--retry", "5"] ++ (if supportLegacyCurl then #[] else #["--retry-all-errors"])

/--
Construct the URL for the cache file `fileName` in repo `repo`, against the
container reachable at `containerURL`.

The `f/` prefix marks files. Whether the rest of the path is
flat (`/f/<fileName>`) or repo-namespaced (`/f/<repo>/<fileName>`) follows the
container (see `Container.flatPath`), not the repo: the same hash under
`repo = MATHLIBREPO` lands flat in `master` and prefixed in `forks`.

`container` is `none` for the user-supplied `MATHLIB_CACHE_GET_URL` /
`MATHLIB_CACHE_PUT_URL` URLs, where no container policy applies; the path then
follows the repo directly — flat for `MATHLIBREPO`, prefixed otherwise.

`repo` is lowercased via `normalizeRepo` so the repo-namespaced path is
case-insensitive in the GitHub owner/repo name.
-/
def mkFileURL (container : Option Container) (repo containerURL fileName : String)
    (repoScope : Option String := none) : String :=
  s!"{containerURL}/{fileDirPath container repo repoScope}/{fileName}"

/--
One download round: the files still missing are requested from `url`, at the
path `mkFileURL container? repo url file scope?`. `container?` is `none` for a
flat endpoint (`MATHLIB_CACHE_GET_URL`, or the public cache read as one URL),
and `scope?` is the per-commit namespace the round reads at. The workflows
(`Cache.Workflow`) build the rounds; `downloadFiles` runs them in order.
-/
structure DownloadRound where
  container? : Option Container
  url : String
  scope? : Option String := none
  deriving BEq, Repr, Inhabited

/-- The full SHA of `HEAD` in `cwd` (`git rev-parse HEAD`); throws when git fails. -/
def getGitCommitHash (cwd : FilePath := ".") : IO String := do
  let out ← IO.Process.output {cmd := "git", args := #["rev-parse", "HEAD"], cwd}
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"git rev-parse HEAD failed (exit code {out.exitCode}):\n{out.stderr.trimAscii}"
  return out.stdout.trimAsciiEnd.copy

section Get

/-- Formats the config file for `curl`, containing the list of files to be downloaded
from a single container's base URL. `scope?` is the per-round SHA scope (see
`mkFileURL`); it is the round's scope, the resolved `--scope` for a normal
read and an individual walked SHA for an `--unsafe` forks round. -/
def mkGetConfigContent (container : Option Container) (repo containerURL : String)
    (hashMap : IO.ModuleHashMap) (scope? : Option String) : IO String := do
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

    -- Note we append `IO.PARTSUFFIX` to the filenames here, which `downloadFiles` then
    -- removes when the download is successful. The suffix carries this process's tag, so a
    -- concurrent `cache` run sharing this `CACHEDIR` writes its own in-flight files, not ours.
    pure <| acc ++ s!"url = {mkFileURL container repo containerURL fileName scope?}\n\
      -o {(IO.CACHEDIR / (fileName ++ IO.PARTSUFFIX)).toString.quote}\n"

/--
Whether an HTTP status returned for a single-file read should be treated as a
cache miss (fall through to the next container in the chain) rather than a
transfer failure worth reporting.

`404` is always a miss. A `403` is a miss only when `treatForbiddenAsMiss` is
set, which callers do for the `legacy` container: when its public read access is
revoked ahead of retirement it answers reads with `403`, and old clients whose
chain still lists `legacy` should fall through quietly instead of printing a
per-file transfer failure. Any other status is a real failure.
-/
def isCacheMissStatus (httpCode : Nat) (treatForbiddenAsMiss : Bool) : Bool :=
  httpCode == 404 || (httpCode == 403 && treatForbiddenAsMiss)

/--
Whether an HTTP status is the one Azure returns for a blob that already exists,
which a non-overwrite `put` (`If-None-Match: *`) hits when it declines to
overwrite. Azure reports it as 409 (the `BlobAlreadyExists` error, what it
returns in practice) or 412 (the conditional-header spec's code for an unmet
`If-None-Match`), so we accept both. Whether that's benign is the caller's call:
the upload path skips it, reads don't.
-/
def isAlreadyPresentStatus (httpCode : Nat) : Bool :=
  httpCode == 409 || httpCode == 412

/-- Direction of a cache transfer. -/
inductive TransferDirection where
  | download
  | upload
  deriving Repr, DecidableEq

instance : ToString TransferDirection where
  toString
    | .download => "download"
    | .upload => "upload"

/-- What one finished transfer amounts to. The index restricts each verdict to
the direction where it has meaning. -/
inductive TransferVerdict : TransferDirection → Type where
  /-- The transfer completed in full. -/
  | delivered {d : TransferDirection} : TransferVerdict d
  /-- The server does not have the file; not an error. -/
  | miss : TransferVerdict .download
  /-- The server already has the file, so there is nothing to transfer; not an
  error. -/
  | skip : TransferVerdict .upload
  /-- The transfer failed. -/
  | failed {d : TransferDirection} : TransferVerdict d
  deriving Repr, DecidableEq

/--
Classify one finished download; the parallel and serial paths share this
table. A transfer delivers only when the status is 200/201 and curl exited
cleanly: a nonzero exit code after a 200 means the body is truncated. The
status alone decides a miss. `httpCode?` is `none` when there is no status
to parse; `treatForbiddenAsMiss` is the `legacy` 403 policy.
-/
def classifyDownload (httpCode? : Option Nat) (exitCode : Nat)
    (treatForbiddenAsMiss : Bool) : TransferVerdict .download :=
  match httpCode? with
  | some 200 | some 201 => if exitCode == 0 then .delivered else .failed
  | some code => if isCacheMissStatus code treatForbiddenAsMiss then .miss else .failed
  | none => .failed

/--
Classify one finished upload. A transfer delivers only on a clean 200/201,
as in `classifyDownload`. With `treatExistsAsSkip` (a non-overwrite put), a
409/412 is a skip: the blob is already on the server. Every other answer, a
404 included, is a failure.
-/
def classifyUpload (httpCode? : Option Nat) (exitCode : Nat)
    (treatExistsAsSkip : Bool) : TransferVerdict .upload :=
  match httpCode? with
  | some 200 | some 201 => if exitCode == 0 then .delivered else .failed
  | some code => if treatExistsAsSkip && isAlreadyPresentStatus code then .skip else .failed
  | none => .failed

/-- Calls `curl` to download a single file from a specific container to `CACHEDIR`
(`.cache`). `scope?` is the per-round SHA scope (see `mkGetConfigContent`).
`treatForbiddenAsMiss` mirrors the parallel path: a `legacy` `403` (public read
access revoked ahead of retirement) is a miss, not a failure. -/
def downloadFile (container : Option Container) (repo containerURL : String)
    (hash : UInt64) (scope? : Option String) (treatForbiddenAsMiss : Bool := false) :
    IO (TransferVerdict .download) := do
  let fileName := hash.asLTar
  let url := mkFileURL container repo containerURL fileName scope?
  let path := IO.CACHEDIR / fileName
  let partFileName := fileName ++ IO.PARTSUFFIX
  let partPath := IO.CACHEDIR / partFileName
  let out ← IO.Process.output
    { cmd := (← IO.getCurl),
      args := #[url, "--silent"] ++ curlFollowRedirectArgs ++
        -- This path serves curls below 7.71, which reject `--retry-all-errors`.
        curlRetryArgs (supportLegacyCurl := true) ++
        #["--write-out", "%{http_code}", "-o", partPath.toString] }
  -- Anything short of a delivery leaves at most an error body in the part file.
  let verdict := classifyDownload out.stdout.trimAscii.toNat? out.exitCode.toNat
    treatForbiddenAsMiss
  if verdict matches .delivered then
    IO.FS.rename partPath path
  else if ← partPath.pathExists then
    IO.FS.removeFile partPath
  return verdict

/-- Extract hash from filename (e.g., "/path/to/.cache/00012345.ltar" → 0x12345).
    Handles a finished `<hash>.ltar`, an in-flight `<hash>.ltar<PARTSUFFIX>`, and a
    `<hash>.ltar.part` left in the cache by a version that wrote untagged temporaries. -/
def hashFromFileName (path : FilePath) : Option UInt64 :=
  let peel (name : String) := (FilePath.mk name).fileStem.getD name
  let name := path.fileName.getD path.toString
  -- Peel one extension at a time — `.part`, this process's tag, `.ltar` — and take the first stem
  -- that parses as a hash, so all three shapes above resolve without knowing which one this is.
  [name, peel name, peel (peel name), peel (peel (peel name))].findSome? String.parseHexToUInt64?

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

/-- Decompression pipeline state, carried from each download round into the
next. A round can end with downloads queued (`pending`) or in a running
leantar batch (`currentTask`); `downloadFiles` hands each round's final state
to the next, and `finalizeDecomp` drains what remains after the last round. -/
structure DecompState where
  /-- Downloaded files waiting to be dispatched in a leantar batch. -/
  pending : Array (FilePath × Lean.Name) := #[]
  /-- The in-flight leantar batch, if any. -/
  currentTask : Option (Task (Except IO.Error Unit)) := none
  /-- Size of the batch `currentTask` is processing. -/
  lastBatchSize : Nat := 0
  /-- Files decompressed, cumulative across rounds. -/
  decompressed : Nat := 0
  /-- Decompression failures, cumulative across rounds. -/
  decompFailed : Nat := 0

structure TransferState where
  last : Nat := 0
  success : Nat := 0
  failed : Nat := 0
  done : Nat := 0
  speed : Nat := 0
  /-- Decompression pipeline state; used only when a `DecompConfig` is set. -/
  decomp : DecompState := {}

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

/-- Drain the decompression pipeline after the last download round: harvest the
in-flight leantar batch, then decompress the pending files. Returns the final
`(decompressed, decompFailed)` counters. -/
def finalizeDecomp (state : DecompState) (config : DecompConfig) : IO (Nat × Nat) := do
  let mut {pending, currentTask, lastBatchSize, decompressed, decompFailed} := state
  if let some task := currentTask then
    let (d, f, err?) := harvestDecompTask task lastBatchSize decompressed decompFailed
    decompressed := d
    decompFailed := f
    if let some e := err? then
      IO.eprintln s!"Decompression error: {e}"
  if !pending.isEmpty then
    try
      decompressBatch pending config.force config.isMathlibRoot config.mathlibDepPath
      decompressed := decompressed + pending.size
    catch e =>
      IO.eprintln s!"Decompression error: {e}"
      decompFailed := decompFailed + pending.size
  return (decompressed, decompFailed)

def monitorCurl {dir : TransferDirection} (args : Array String) (size : Nat)
    (caption : String) (speedVar : String)
    (classify : Option Nat → Nat → TransferVerdict dir) (removeOnError := false)
    (decompConfig : Option DecompConfig := none)
    (decompState : DecompState := {}) : IO (TransferState × Std.HashSet UInt64) := do
  let useAnsi := (← IO.getEnv "TERM").isSome
  -- Hashes of the files this pass fetched, used to decide what the next
  -- container in the chain still needs to retry.
  let servedRef ← IO.mkRef (∅ : Std.HashSet UInt64)
  let mkStatus (s : TransferState) : String := Id.run do
    let speedStr :=
      if s.speed != 0 then
        s!", {s.speed / 1000} KB/s"
      else ""
    let mut msg := s!"\r{caption}: {s.success} file(s) [attempted {s.done}/{size} = {100*s.done/size}%{speedStr}]"
    -- Add decompression progress if enabled
    if decompConfig.isSome then
      msg := msg ++ s!", Decompressed: {s.decomp.decompressed}"
      if s.decomp.decompFailed != 0 then
        msg := msg ++ s!" ({s.decomp.decompFailed} failed)"
    if s.failed != 0 then
      msg := msg ++ s!", {s.failed} {dir} failed"
    -- Clear to end of line to avoid remnants from longer previous messages
    if useAnsi then
      msg := msg ++ "\x1b[K"
    return msg
  let init : TransferState := { last := (← IO.monoMsNow), decomp := decompState }
  let s ← IO.runCurlStreaming args init fun a line => do
    let mut {last, success, failed, done, speed, decomp} := a
    let mut {pending, currentTask, lastBatchSize, decompressed, decompFailed} := decomp
    -- Classify each finished transfer: rename a delivered part file, report a
    -- failure, and remove the part file on any non-delivery.
    let line := line.trimAscii
    if !line.isEmpty then
      match Lean.Json.parse line.copy with
      | .ok result =>
        let code? := result.getObjValAs? Nat "http_code"
        let fn? := result.getObjValAs? String "filename_effective"
        -- The per-transfer JSON report carries `exitcode` from curl 7.75 on;
        -- an absent field reads as 0.
        let exitCode := (result.getObjValAs? Nat "exitcode").toOption.getD 0
        let verdict := classify code?.toOption exitCode
        if verdict matches .delivered then
          if let .ok fn := fn? then
            -- Match this process's own suffix, not a bare `.part`: a concurrent run's
            -- in-flight file is not ours to rename, and curl only reports our transfers.
            if (← System.FilePath.pathExists fn) && fn.endsWith IO.PARTSUFFIX then
              let finalPath := (fn.dropEnd IO.PARTSUFFIX.length).copy
              IO.FS.rename fn finalPath
              let hash? := hashFromFileName finalPath
              if let some hash := hash? then servedRef.modify (·.insert hash)
              -- Add to decompression queue if enabled
              if let some config := decompConfig then
                let some hash := hash? | do
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
        else
          if verdict matches .failed then
            failed := failed + 1
            let mkFailureMsg code? fn? msg? : String := Id.run do
              let mut msg := "Transfer failed"
              if let .ok fn := fn? then
                msg := s!"{fn}: {msg}"
              if let .ok code := code? then
                msg := s!"{msg} (error code: {code})"
              if exitCode != 0 then
                msg := s!"{msg} (curl exit code: {exitCode})"
              if let .ok errMsg := msg? then
                msg := s!"{msg}: {errMsg}"
              return msg
            let msg? := result.getObjValAs? String "errormsg"
            -- A download is named by its part file, an upload by its URL.
            -- The URL is query-stripped, so a credential in the query string
            -- is not printed.
            let src? : Except String String := match dir with
              | .download => fn?
              | .upload =>
                (result.getObjValAs? String "url_effective").map
                  fun url => (url.splitOn "?").headD url
            IO.println (mkFailureMsg code? src? msg?)
          -- The part file holds a truncated body (failure) or an error body
          -- (miss); remove it either way.
          if removeOnError then
            if let .ok fn := fn? then
              -- `curl --remove-on-error` can already do this, but only from 7.83 onwards
              if (← System.FilePath.pathExists fn) && fn.endsWith IO.PARTSUFFIX then
                IO.FS.removeFile fn
        done := done + 1
        let now ← IO.monoMsNow
        if now - last ≥ 100 then -- max 10/s update rate
          speed := match result.getObjValAs? Nat speedVar with
            | .ok speed => speed | .error _ => speed
          let decompNow : DecompState :=
            {pending, currentTask, lastBatchSize, decompressed, decompFailed}
          IO.eprint (mkStatus {last, success, failed, done, speed, decomp := decompNow})
          last := now
       | .error e =>
        IO.println s!"Non-JSON output from curl:\n  {line}\n{e}"
    let decompNow : DecompState :=
      {pending, currentTask, lastBatchSize, decompressed, decompFailed}
    pure {last, success, failed, done, speed, decomp := decompNow}
  if s.done > 0 then
    -- to avoid confusingly moving on without finishing the count
    IO.eprintln (mkStatus s)
  return (s, ← servedRef.get)

/-- Run one container's download pass for the given hash map. Returns the
`TransferState` from `monitorCurl` (synthesized in serial mode, where it
carries only the transfer-failure count) and the set of hashes it fetched, so
the caller can carry the rest to the next container. `decompState` is the
previous round's decompression pipeline state; the returned state's `decomp`
continues it. Serial mode never pipelines and passes it through untouched.
Side effect: fetched files are written to `CACHEDIR` with their final names. -/
private def downloadFilesFromContainer
    (container : Option Container) (repo containerURL : String)
    (hashMap : IO.ModuleHashMap)
    (parallel : Bool) (decompConfig : Option DecompConfig)
    (scope? : Option String) (decompState : DecompState) :
    IO (TransferState × Std.HashSet UInt64) := do
  let size := hashMap.size
  -- `legacy` answers reads with 403 once its public access is revoked ahead
  -- of retirement; treat that as a miss so the chain stays quiet for clients
  -- whose chain still lists it.
  let treatForbiddenAsMiss := container == some Container.legacy
  if parallel then
    IO.FS.writeFile IO.CURLCFG (← mkGetConfigContent container repo containerURL hashMap scope?)
    let args := #["--request", "GET", "--parallel", "--silent"] ++
      -- Avoid passing `--fail` here: it slows parallel transfers on curl
      -- 8.13.0, and it makes `--retry-all-errors` retry every 404 miss.
      curlFollowRedirectArgs ++ curlRetryArgs (supportLegacyCurl := false) ++
      #["--write-out", "%{json}\n", "--config", IO.CURLCFG.toString]
    let (s, served) ← monitorCurl args size "Downloaded" "speed_download"
      (classifyDownload · · treatForbiddenAsMiss) (removeOnError := true)
      decompConfig decompState
    IO.FS.removeFile IO.CURLCFG
    return (s, served)
  else
    let r ← hashMap.foldM (init := []) fun acc _ hash => do
      pure <| (hash, ← IO.asTask do
        downloadFile container repo containerURL hash scope? treatForbiddenAsMiss) :: acc
    -- Served hashes carry the remaining files to the next container; hard
    -- failures (anything but a 404/legacy-403 miss, including a task that threw)
    -- feed `TransferState.failed`, so they drive the exit code exactly as the
    -- parallel path threads its own `failed` count.
    let (served, failed) := r.foldl (init := ((∅ : Std.HashSet UInt64), 0))
      fun (served, failed) (hash, t) =>
        match t.get with
        | .ok .delivered => (served.insert hash, failed)
        | .ok .miss => (served, failed)
        | _ => (served, failed + 1)
    return ({ failed, decomp := decompState }, served)

/-- Call `curl` to download files from the server to `CACHEDIR` (`.cache`).
Return the number of files which failed to download.
If `decompress` is true, decompresses files as they're downloaded (pipelined).

`rounds` are the download rounds the workflow resolved, in order (see
`DownloadRound`). After each round, files that were successfully fetched are
filtered out so the next round only retries genuine misses.

With `reportScopes` (set by `cache get --unsafe`) the summary reports which
scoped rounds supplied files. -/
def downloadFiles
    (rounds : List DownloadRound) (repo : String) (hashMap : IO.ModuleHashMap)
    (forceDownload : Bool) (parallel : Bool) (warnOnMissing : Bool)
    (decompress : Bool := false) (forceUnpack : Bool := false)
    (isMathlibRoot : Bool := false) (mathlibDepPath : FilePath := ".")
    (reportScopes : Bool := false) : IO Nat := do
  let hashMap ← if forceDownload then pure hashMap else hashMap.filterExists false
  if hashMap.isEmpty then IO.println "No files to download"; return 0
  IO.FS.createDirAll IO.CACHEDIR

  if rounds.isEmpty then
    IO.eprintln "No cache URLs configured for download"
    return hashMap.size

  -- Set up decompression config if enabled: one config shared by all container
  -- rounds, with the pipeline state carried between them via `decompState`.
  let decompConfig ← if decompress then
    let hashToMod : Std.HashMap UInt64 Lean.Name := hashMap.fold (init := ∅) fun acc mod hash =>
      acc.insert hash mod
    pure (some { hashToMod, force := forceUnpack, isMathlibRoot, mathlibDepPath : DecompConfig })
  else
    pure none

  -- Walk the rounds in trust order. After each round, drop files that
  -- succeeded so the next round only retries genuine misses.
  let mut remaining := hashMap
  -- Decompression pipeline state, carried from each round into the next (see
  -- `DecompState`); `finalizeDecomp` below drains what the last round leaves.
  let mut decompState : DecompState := {}
  -- Hard transfer failures (not 404 misses) drive the exit code; misses are
  -- normal and instead surface as the "not found" hint keyed on `remaining`.
  -- Accumulated across rounds: a failure in an early container counts even
  -- when a later round serves the file.
  let mut downloadFailed := 0
  -- For the `--unsafe` summary: how many files each scoped (forks) round supplied,
  -- attributed by the drop in `remaining` across that round.
  let mut scopeServed : Array (String × Nat) := #[]
  for round in rounds do
    if remaining.isEmpty then break
    let scopeNote := match round.scope? with | some s => s!" (scope {s})" | none => ""
    IO.println s!"Attempting to download {remaining.size} file(s) from {repo} cache at \
      {round.url}{scopeNote}"
    let before := remaining.size
    let (s, served) ← downloadFilesFromContainer round.container? repo round.url remaining
      parallel decompConfig round.scope? decompState
    -- Carry the decompression pipeline into the next round and the drain
    -- below: files left behind here are never decompressed. Drop the files
    -- this round served so the next container only retries genuine misses,
    -- regardless of what is already on disk.
    decompState := s.decomp
    downloadFailed := downloadFailed + s.failed
    remaining := remaining.filter fun _ hash => !served.contains hash
    if reportScopes then
      if let some sha := round.scope? then
        scopeServed := scopeServed.push (sha, before - remaining.size)

  -- `--unsafe`: report which fork commits actually contributed files, so the
  -- user knows whose artifacts they ended up trusting.
  if reportScopes then
    if scopeServed.isEmpty then
      IO.eprintln "--unsafe: no fork scopes were needed; \
        all files were served by higher-trust containers."
    else
      IO.eprintln s!"--unsafe: cache served from {scopeServed.size} fork commit scope(s):"
      for (sha, n) in scopeServed do
        IO.eprintln s!"  {sha} → {n} file(s)"
      if remaining.size > 0 then
        IO.eprintln s!"  {remaining.size} file(s) still missing after all scopes."

  if warnOnMissing && !remaining.isEmpty then
    IO.eprintln "Warning: some files were not found in the cache."
    IO.eprintln "This usually means that your local checkout of mathlib4 has diverged from upstream."
    IO.eprintln ""
    IO.eprintln "  * If you push your commits to a PR to the mathlib4 repository"
    IO.eprintln "    (use a draft PR if it is not ready for review),"
    IO.eprintln "    then CI will build the oleans and they will be available later."
    IO.eprintln "  * If you have already opened a PR, this may mean"
    IO.eprintln "    the CI build has failed part-way through building."

  -- Drain the decompression pipeline accumulated across all rounds.
  if let some config := decompConfig then
    let (decompressed, decompFailed) ← finalizeDecomp decompState config
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

/-- Downloads missing files, and unpacks files.

`rounds` are the download rounds the workflow resolved (see `Cache.Workflow`);
`repo` is the resolved repo they read for. This function is the shared read
mechanism under every workflow: the toolchain and manifest checks of a project
that depends on Mathlib, the download rounds, and the decompression. -/
def getFiles
    (rounds : List DownloadRound) (repo : String) (hashMap : IO.ModuleHashMap)
    (forceDownload forceUnpack parallel decompress : Bool)
    (reportScopes : Bool := false)
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
    if let some plan ← IO.prepareDecompConfig hashMap forceUnpack then
      if plan.alreadyDecompressed > 0 then
        IO.println s!"Decompressing {plan.needsDecomp} already-cached file(s) \
          ({plan.alreadyDecompressed} already decompressed)"
      else
        IO.println s!"Decompressing {plan.needsDecomp} already-cached file(s)"
      let task ← IO.asTask (IO.spawnLeanTarDecompress plan.config forceUnpack)
      pure (some (task, plan.needsDecomp))
    else pure none
  else pure none

  let failed ← downloadFiles rounds repo hashMap forceDownload parallel
    (warnOnMissing := true)
    (decompress := decompress) (forceUnpack := forceUnpack)
    isMathlibRoot mathlibDepPath (reportScopes := reportScopes)
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

end Cache.Requests
