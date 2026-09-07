/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster, Marcelo Lynch
-/

import Cache.Cli
import Cache.Requests
import Cache.Marker
import Cache.Query
import Cache.Warning

def help : String := "Mathlib4 caching CLI
Usage: cache [OPTIONS] [COMMAND]

Commands:
  # No privilege required
  get  [ARGS]    Download linked files missing on the local cache and decompress
  get! [ARGS]    Download all linked files and decompress
  get- [ARGS]    Download linked files missing to the local cache, but do not decompress
  pack           Compress non-compressed build files into the local cache
  pack!          Compress build files into the local cache (no skipping)
  unpack         Decompress linked already downloaded files
  unpack!        Decompress linked already downloaded files (no skipping)
  clean          Delete non-linked files
  clean!         Delete everything on the local cache
  lookup [ARGS]  Show information about cache files for the given Lean files
  query [REF]    Without REF: find most recent cached commit on this branch.
                 With REF (e.g. HEAD, a SHA): boolean probe; exit 0 if cached, 1 if not.

  # Privilege required
  put          Run 'pack' then upload linked files missing on the server
  put!         Run 'pack' then upload all linked files
  commit       Write a commit on the server
  commit!      Overwrite a commit on the server

  # Intended for CI use
  unstage      Copy *.ltar files from the staging directory to the local cache
  unstage!     Copy *.ltar files from the staging directory to the local cache (overwrite existing files)
  stage        Move files not already 'pack'ed to an output directory
  stage!       Move all linked cache files to an output directory
  put-staged   Upload *.ltar files from the staging directory (privilege required)
  put-unpacked Run 'put' only for files not already 'pack'ed (privilege required)

Options:
  --repo=OWNER/REPO  Override the repository to fetch/push cache from
  --staging-dir=<output-directory> Required for 'stage', 'stage!', 'unstage' and 'put-staged': staging directory.
  --cache-from=LIST  Comma-separated, trust-ordered list of containers to read from
                     (e.g. `--cache-from=master,forks`). Overrides the per-repo default.
                     Known containers: master, forks, nightly-testing,
                     pr-toolchain-tests, legacy.
  --scope=REF        Read the fork SHA-scoped namespace at the given commit ref
                     (any git ref `git rev-parse` accepts: HEAD, branch, tag, SHA)
                     instead of the default, the checked-out HEAD. Use the SHA
                     reported by `cache query`. Wins over the
                     MATHLIB_CACHE_REPO_SCOPE env var. Reading another commit's
                     scope means trusting the artifacts produced at that commit;
                     `cache get` prints a security notice when the scope differs
                     from HEAD.
  --unsafe           (get only) Instead of pinning one --scope, automatically walk
                     this branch's history and try the most recent cached fork
                     commits as scopes, in order, until the cache is satisfied.
                     Trusts the artifacts of every commit it tries. Mutually
                     exclusive with --scope; always prints a security notice.
  --unsafe-window=N  Number of cached fork commits --unsafe will try (default
                     1). Implies --unsafe.
  --container=NAME   Target container for upload commands (put/put!/put-unpacked/
                     put-staged/commit/commit!). Known containers: master, forks,
                     nightly-testing, pr-toolchain-tests, legacy. Pass this
                     explicitly; with neither it nor MATHLIB_CACHE_PUT_URL set,
                     the upload falls back to `legacy` and warns.

* Linked files refer to local cache files with corresponding Lean sources
* Commands ending with '!' should be used manually, when hot-fixes are needed

# The arguments for 'get', 'get!', 'get-' and 'lookup'

'get', 'get!', 'get-' and 'lookup' can process a list of module names or file names.

'get [ARGS]' will only get the cache for the specified Lean files and all files imported by one.

Valid arguments are:

* Module names like 'Mathlib.Init'
* Module globs like 'Mathlib.Data.+' (find all Lean files inside `Mathlib/Data/`)
* Module globs like 'Mathlib.Data.*' (both of the above)
* File names like 'Mathlib/Init.lean'
* Folder names like 'Mathlib/Data/' (find all Lean files inside `Mathlib/Data/`)
* With bash's automatic glob expansion one can also write things like
  'Mathlib/**/Order/*.lean'. However, one would need to write `Mathlib.Data.\\*`
  to prevent glob expansion.

# Environment variables

* MATHLIB_CACHE_DIR       Local cache directory (default: ~/.cache/mathlib)
* MATHLIB_CACHE_GET_URL   Download from this single URL, bypassing the containers
* MATHLIB_CACHE_PUT_URL   Upload to this single URL, bypassing the containers
* MATHLIB_CACHE_FROM      Comma-separated container list for reads, same shape as
                          --cache-from. Used by CI to widen reads per job;
                          --cache-from takes precedence when both are set.

See Cache/README.md for more details.
"

/-- Commands which (potentially) call `curl` for downloading files -/
def curlArgs : List String :=
  ["get", "get!", "get-", "put", "put!", "put-unpacked", "put-staged", "commit", "commit!"]

/-- Commands which (potentially) call `leantar` for compressing or decompressing files -/
def leanTarArgs : List String :=
  ["get", "get!", "put", "put!", "put-unpacked", "pack", "pack!", "unpack", "lookup", "stage", "stage!"]

open Cache Cli IO Hashing Requests System in
def main (args : List String) : IO Unit := do
  if args.isEmpty || parseFlagOpt "help" args then
    println help
    Process.exit 0
  CacheM.run do

  -- split args and named options
  let (options, args) := args.partition (·.startsWith "--")

  -- check for unrecognized options
  for opt in options do
    unless isKnownOpt opt do
      IO.eprintln s!"Unknown option '{opt}'"
      IO.eprintln help
      Process.exit 1

  let repo? ← parseNamedOpt "repo" options
  let stagingDir? ← parseNamedOpt "staging-dir" options
  let cacheFromStr? ← parseNamedOpt "cache-from" options
  let containerStr? ← parseNamedOpt "container" options
  let scopeStr? ← parseNamedOpt "scope" options
  let unsafeFlag := parseFlagOpt "unsafe" options
  let unsafeWindowStr? ← parseNamedOpt "unsafe-window" options

  -- Resolve `--unsafe` / `--unsafe-window=N` into an optional SHA window.
  -- `some n` means unsafe mode is on with window `n`; `none` means off. Passing
  -- `--unsafe-window` implies `--unsafe`.
  let unsafeWindow? : Option Nat ← match unsafeWindowStr? with
    | some s => match s.toNat? with
      | some n =>
        if n == 0 then
          IO.eprintln "--unsafe-window must be a positive integer"
          Process.exit 1
        pure (some n)
      | none =>
        IO.eprintln s!"--unsafe-window must be a positive integer (got '{s}')"
        Process.exit 1
    | none => pure (if unsafeFlag then some defaultUnsafeSHAWindow else none)

  -- `--unsafe` and `--scope` are mutually exclusive: `--unsafe` walks several
  -- commit scopes automatically, `--scope` pins exactly one.
  if unsafeWindow?.isSome && scopeStr?.isSome then
    IO.eprintln "--unsafe and --scope are mutually exclusive: --unsafe walks several commit \
      scopes automatically, while --scope pins exactly one."
    Process.exit 1

  -- Apply `--scope=` to the process-wide override read by `getRepoScope`.
  -- Accepts any git ref `git rev-parse` resolves (HEAD, branch, tag, SHA);
  -- falls through to the literal value if `git rev-parse` is unavailable
  -- (e.g. invoked outside a git checkout with a bare SHA).
  if let some s := scopeStr? then
    let resolved ← try resolveGitRef s catch _ => pure s
    scopeOverride.set (some resolved)

  -- Apply `--cache-from` to the process-wide override read by `effectiveGetURLs`.
  if let some s := cacheFromStr? then
    match parseCacheFromList s with
    | none =>
      IO.eprintln s!"Unknown container name in --cache-from={s}.\n\
        Known containers: {", ".intercalate (Container.all.map Container.name)}."
      Process.exit 1
    | some cs => cacheFromOverride.set (some cs)

  -- Parse `--container=NAME`. Validation is unconditional; the upload commands
  -- enforce that the flag is set (via `effectiveUploadURL`).
  let container? ← match containerStr? with
    | none => pure none
    | some s => match Container.parse? s with
      | some c => pure (some c)
      | none =>
        IO.eprintln s!"Unknown container name in --container={s}.\n\
          Known containers: {", ".intercalate (Container.all.map Container.name)}."
        Process.exit 1

  -- Early dispatch for `query`: avoids running `parseArgs` (which would try to
  -- interpret a git ref like `HEAD` as a Lean module) and skips the expensive
  -- hash-memo build below — the query only needs git + a single HTTP probe.
  match args with
  | ["query"] =>
    let repo ← resolveQueryRepo repo?
    cacheQuery repo (cap := 50)
    return
  | ["query", ref] =>
    let repo ← resolveQueryRepo repo?
    let sha ← resolveGitRef ref
    cacheQuerySingle repo sha
    return
  | "query" :: _ =>
    IO.eprintln "Usage: cache query [REF]"
    Process.exit 1
  | _ => pure ()

  let mut roots : Std.HashMap Lean.Name FilePath ← parseArgs args
  if roots.isEmpty then do
    -- No arguments means to start from `Mathlib.lean`
    -- TODO: could change this to the default-target of a downstream project
    let mod := `Mathlib
    let sp := (← read).srcSearchPath
    let sourceFile ← Lean.findLean sp mod
    roots := roots.insert mod sourceFile

  let hashMemo ← getHashMemo roots
  let hashMap := hashMemo.hashMap
  let goodCurl ← pure !curlArgs.contains (args.headD "") <||> validateCurl
  let get (args : List String) (force := false) (decompress := true) := do
    let hashMap ← if args.isEmpty then pure hashMap else hashMemo.filterByRootModules roots.keys
    -- Resolve the repo once (single git-remote probe) and thread it through the
    -- read path, the non-default-scope warning, and the HEAD hint below.
    let cliOverride? ← cacheFromOverride.get
    let (detectedRepo?, resolvedRepo) ← resolveRepo repo? (← read).mathlibDepPath
    -- Warn before reading if the scope is non-default (`--unsafe` always is).
    warnIfNonDefaultScope repo? detectedRepo? cliOverride? resolvedRepo unsafeWindow?
    -- In `--unsafe` mode, walk history for recent cached fork commits to try as
    -- scopes; otherwise point an uncached fork HEAD at the per-commit workflow.
    let unsafeScopes ← match unsafeWindow? with
      | some window =>
        let scopes ← discoverUnsafeScopes resolvedRepo window
        if scopes.isEmpty then
          IO.eprintln s!"--unsafe: no cached fork commits found in range for {resolvedRepo}; \
            reading the default cache only."
        else
          IO.eprintln s!"--unsafe: trying {scopes.length} cached fork commit scope(s) for \
            {resolvedRepo} (most recent first):"
          for s in scopes do IO.eprintln s!"  {s}"
        pure scopes
      | none =>
        informIfHeadNotBuilt resolvedRepo
        pure []
    getFiles resolvedRepo hashMap force force goodCurl decompress (unsafeScopes := unsafeScopes)
  let pack (overwrite verbose unpackedOnly := false) := do
    packCache hashMap overwrite verbose unpackedOnly (← getGitCommitHash)
  let put (overwrite unpackedOnly := false) := do
    let repo := repo?.getD MATHLIBREPO
    let auth ← getUploadAuth
    putFiles repo container? (← pack overwrite (verbose := true) unpackedOnly) overwrite auth
    if let some sha ← getRepoScope then
      if let some c := container? then
        uploadMarker c repo sha auth
  let stage outDir (unpackedOnly := true) := do
    stageFiles outDir (← pack (verbose := true) (unpackedOnly := unpackedOnly))
  let unstage (overwrite := false) := do
    if stagingDir?.isNone then IO.println "unstage requires --staging-dir=" return else
      unstageFiles stagingDir?.get! overwrite
  let putStaged (stagingDir : FilePath) := do
    let repo := repo?.getD MATHLIBREPO
    if !(←stagingDir.isDir) then IO.println "--staging-dir must be a directory" return
    else
      let fileSet ← getFilesWithExtension stagingDir "ltar"
      let auth ← getUploadAuth
      putFilesAbsolute repo container? fileSet (tempConfigFilePath := stagingDir / "curl.config")
        (overwrite := false) auth
      -- After artifacts upload, write the per-SHA marker if the upload is
      -- SHA-scoped. The marker lets `cache query` discover cached commits
      -- with a cheap HEAD probe.
      if let some sha ← getRepoScope then
        if let some c := container? then
          uploadMarker c repo sha auth

  match args with
  | "get"  :: args => get args
  | "get!" :: args => get args (force := true)
  | "get-" :: args => get args (decompress := false)
  | ["pack"] => discard <| pack
  | ["pack!"] => discard <| pack (overwrite := true)
  | ["unpack"] => unpackCache hashMap false
  | ["unpack!"] => unpackCache hashMap true
  | ["unstage"] => unstage
  | ["unstage!"] => unstage (overwrite := true)
  | ["clean"] =>
    cleanCache <| hashMap.fold (fun acc _ hash => acc.insert <| CACHEDIR / hash.asLTar) .empty
  | ["clean!"] => cleanCache
  -- We allow arguments for `put*` so they can be added to the `roots`.
  | "put" :: _ => put
  | "put!" :: _ => put (overwrite := true)
  | "put-unpacked" :: _ => put (unpackedOnly := true)
  | "stage" :: _ => if (stagingDir?.isNone) then IO.println "stage requires --staging-dir=" return else
    stage stagingDir?.get!
  | "stage!" :: _ => if (stagingDir?.isNone) then IO.println "stage! requires --staging-dir=" return else
    stage stagingDir?.get! (unpackedOnly := false)
  | "put-staged" :: _ => if (stagingDir?.isNone) then IO.println "put-staged requires --staging-dir=" return else
    putStaged stagingDir?.get!
  | ["commit"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit container? hashMap false (← getUploadAuth)
  | ["commit!"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit container? hashMap true (← getUploadAuth)
  | ["collect"] => IO.println "TODO"
  | "lookup" :: _ => lookup hashMap roots.keys
  | [] => println help -- unreachable: options are already partitioned out
  | cmd :: _ =>
    IO.eprintln s!"Unknown command '{cmd}'"
    IO.eprintln help
    Process.exit 1
