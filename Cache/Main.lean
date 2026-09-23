/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster, Marcelo Lynch
-/

import Cache.Cli
import Cache.Requests
import Cache.Marker
import Cache.Upload
import Cache.Query
import Cache.Warning

/-- The known container names, interpolated into the help text so the list
always matches `Container.all`. -/
def knownContainersLine : String :=
  ", ".intercalate (Cache.Requests.Container.all.map Cache.Requests.Container.name)

def help : String := "Mathlib4 caching CLI
Usage: cache [OPTIONS] [COMMAND]

Commands:
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

  # Staging
  stage        Move files not already 'pack'ed to an output directory
  stage!       Move all linked cache files to an output directory
  unstage      Copy *.ltar files from the staging directory to the local cache
  unstage!     Copy *.ltar files from the staging directory to the local cache (overwrite existing files)

The upload commands (put, put!, put-staged) and their options and variables
are internal to mathlib CI. To operate an external cache, 'stage' the
artifacts, upload the staging directory under your endpoint's `f/` path with
any storage client, and serve it to readers via MATHLIB_CACHE_GET_URL.

Options:
  --repo=OWNER/REPO  Override the repository to fetch cache for
  --staging-dir=<output-directory> Required for 'stage', 'stage!', 'unstage'
                     and 'unstage!': staging directory.
  --cache-from=LIST  Comma-separated, trust-ordered list of containers to read from
                     (e.g. `--cache-from=master,forks`). Overrides the per-repo default.
                     Known containers: " ++ knownContainersLine ++ ".
  --scope=REF        The per-commit namespace (any git ref `git rev-parse`
                     accepts: HEAD, branch, tag, SHA). For reads: the fork
                     SHA-scoped namespace to read instead of the default, the
                     checked-out HEAD. Use the SHA reported by `cache query`.
                     Reading another commit's scope means trusting the
                     artifacts produced at that commit; `cache get` prints a
                     security notice when the scope differs from HEAD.
  --unsafe           (get only) Instead of pinning one --scope, automatically walk
                     this branch's history and try the most recent cached fork
                     commits as scopes, in order, until the cache is satisfied.
                     Trusts the artifacts of every commit it tries. Mutually
                     exclusive with --scope; always prints a security notice.
  --unsafe-window=N  Number of cached fork commits --unsafe will try (default
                     1). Implies --unsafe.

* Linked files refer to local cache files with corresponding Lean sources
* Commands that end with '!' do not skip files: use them manually when a
  hot-fix must force a re-download, a re-pack, or an overwrite

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
* MATHLIB_CACHE_DEBUG_USE_LEGACY
                          Set to 1 or true to read from the Azure storage
                          account instead of https://cache.mathlib.org.
                          For troubleshooting only.
* MATHLIB_CACHE_GET_URL   Download from this single URL as a flat namespace.
                          Allows third parties to use their own cache endpoint.
                          An empty value means unset.
"

/-- Commands which download with `curl`. Uploads validate curl inside the
curl tool (`putStagedViaCurl`), when a backend selects it. -/
def curlArgs : List String :=
  ["get", "get!", "get-"]

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

  -- Resolve the legacy switch once, before anything builds a read URL.
  useLegacy.set (← getEnvFlag "MATHLIB_CACHE_DEBUG_USE_LEGACY" (ifUnset := false))

  let repo? ← parseNamedOpt "repo" options
  let stagingDir? ← parseNamedOpt "staging-dir" options
  let cacheFromStr? ← parseNamedOpt "cache-from" options
  let containerStr? ← parseNamedOpt "container" options
  let scopeStr? ← parseNamedOpt "scope" options
  let unsafeFlag := parseFlagOpt "unsafe" options
  let unsafeWindowStr? ← parseNamedOpt "unsafe-window" options
  let backendStr? ← parseNamedOpt "backend" options

  -- Parse `--backend=NAME`; `azure` is the default.
  let backend ← match backendStr? with
    | none => pure UploadBackend.azure
    | some s => match UploadBackend.parse? s with
      | some b => pure b
      | none =>
        IO.eprintln s!"Unknown backend name in --backend={s}.\n\
          Known backends: {", ".intercalate (UploadBackend.all.map UploadBackend.name)}."
        Process.exit 1

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

  -- Parse `--container=NAME`. Validation is unconditional; `put` enforces that
  -- the flag is set (via `stagedUploadDest`).
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
  -- `put-staged` uploads the staging directory: it does not need the hash
  -- memo, so it dispatches here, with `query`, before the expensive build
  -- below.
  | ["put-staged"] =>
    let some stagingDir := stagingDir? | do
      IO.eprintln "put-staged requires --staging-dir= (it uploads a staged set; \
        produce one with `cache pack` and `cache stage --staging-dir=DIR`, \
        or pack-and-upload in one step with `cache put`)"
      Process.exit 1
    let stagingDir : FilePath := stagingDir
    if !(← stagingDir.isDir) then
      IO.eprintln "--staging-dir must be a directory"
      Process.exit 1
    runPut container? repo? backend stagingDir (overwrite := false)
      (getFileNames := do
        return (← getFilesWithExtension stagingDir "ltar").map (·.fileName.get!))
    return
  | "put-staged" :: _ =>
    IO.eprintln "Usage: cache put-staged --staging-dir=DIR [--container=NAME] \
      [--repo=OWNER/REPO] [--scope=REF] [--backend=NAME]"
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
  -- `pack`-and-upload: the hash memo scopes the file list to what this
  -- checkout's build links, so nothing else in the shared per-user cache
  -- directory is uploaded.
  let put (overwrite := false) :=
    runPut container? repo? backend IO.CACHEDIR
      (getFileNames := pack overwrite (verbose := true)) overwrite
  let stage outDir (unpackedOnly := true) := do
    stageFiles outDir (← pack (verbose := true) (unpackedOnly := unpackedOnly))
  let unstage (overwrite := false) := do
    if stagingDir?.isNone then IO.println "unstage requires --staging-dir=" return else
      unstageFiles stagingDir?.get! overwrite

  match args with
  | "get"  :: args => get args
  | "get!" :: args => get args (force := true)
  | "get-" :: args => get args (decompress := false)
  | ["pack"] => discard <| pack
  | ["pack!"] => discard <| pack (overwrite := true)
  | ["unpack"] => unpackCache hashMap false
  | ["unpack!"] => unpackCache hashMap true
  -- We allow arguments for `put*` so they can be added to the roots.
  | "put" :: _ => put
  | "put!" :: _ => put (overwrite := true)
  | ["unstage"] => unstage
  | ["unstage!"] => unstage (overwrite := true)
  | ["clean"] =>
    cleanCache <| hashMap.fold (fun acc _ hash => acc.insert <| CACHEDIR / hash.asLTar) .empty
  | ["clean!"] => cleanCache
  | "stage" :: _ => if (stagingDir?.isNone) then IO.println "stage requires --staging-dir=" return else
    stage stagingDir?.get!
  | "stage!" :: _ => if (stagingDir?.isNone) then IO.println "stage! requires --staging-dir=" return else
    stage stagingDir?.get! (unpackedOnly := false)
  | ["collect"] => IO.println "TODO"
  | "lookup" :: _ => lookup hashMap roots.keys
  | [] => println help -- unreachable: options are already partitioned out
  | cmd :: _ =>
    IO.eprintln s!"Unknown command '{cmd}'"
    IO.eprintln help
    Process.exit 1
