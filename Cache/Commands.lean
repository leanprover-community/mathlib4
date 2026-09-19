/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster, Marcelo Lynch
-/

import Cache.Workflow
import Cache.Upload

/-!
# The `cache` command tree

The commands of `lake exe cache`, parsed by the `Cli` library: each command
declares its flags and arguments, and its handler runs it. `get` is the
command whose behavior depends on the checkout and the environment: it
declares the flags of every read workflow (`Workflow.flags`), decides the
workflow (`Cache.Workflow`), and hands it the parsed command line, from which
the workflow reads its own flags. A `put` decides its URL and its form
(`Upload.decide`) from `MATHLIB_CACHE_PUT_URL` and `--dev-cache`, or from the
well-known container `--container` names; `query` is a developer-cache
command; the local commands (`pack`, `unpack`, `clean`,
`lookup`, and the staging commands) depend on none of this. `main` is the
entry point.
-/

namespace Cache.Commands

open Cache.Requests Cache.Workflow Cache.IO Cache.Hashing
open Cli (Cmd Parsed Arg)
open System (FilePath)

/-- The `.lean` files or modules a command works on. -/
def modulesArg : Arg := {
  name := "modules"
  description := "Module names (Mathlib.Init), module globs (Mathlib.Data.+ for the files \
    under Mathlib/Data/, Mathlib.Data.* for both), file names (Mathlib/Init.lean) or folders \
    (Mathlib/Data/). Without arguments: Mathlib and everything it imports."
  type := String }

/-- The information appended to the root help. -/
def furtherInformation : String := "ARGUMENTS
    get, get!, get-, lookup, put and stage take modules: `get Mathlib.Init` reads
    the cache of that module and of everything it imports. With bash's glob
    expansion one can also write `Mathlib/**/Order/*.lean`; write `Mathlib.Data.\\*`
    to prevent the expansion.

    Commands that end with `!` do not skip files: use them manually when a
    hot-fix must force a re-download, a re-pack, or an overwrite. Linked files
    are the local cache files with corresponding Lean sources.

    A flag may precede the command: `cache --repo=OWNER/REPO get` reads as
    `cache get --repo=OWNER/REPO`.

WORKFLOWS
    get runs one of three workflows, chosen from the repository the checkout
    names (its git remote, or --repo) and the flags. Each workflow accepts its
    own flags and rejects the others'.

    public cache: a canonical mathlib checkout, a project that depends on
        Mathlib, or any get with MATHLIB_CACHE_GET_URL set. get fetches from the
        public cache at https://cache.mathlib.org/mathlib4 (or from that URL)
        and nothing else. No flags of its own.
    developer cache: a fork checkout, or any get with --cache-from, --scope or
        --unsafe (or MATHLIB_CACHE_FROM, MATHLIB_CACHE_REPO_SCOPE set). get walks
        the trust-ordered container chain: master from the public cache, the
        fork's per-commit namespace in forks from the developer cache at
        https://devcache.mathlib.org, then legacy. Flags: --cache-from, --scope,
        --unsafe, --unsafe-window.
    nightly: the nightly-testing repository. get walks its own chain in the
        developer cache: nightly-testing, forks, legacy. Flags: --cache-from,
        --scope.

    In a project that depends on Mathlib, a fork remote on the dependency
    checkout does not select the developer-cache workflow; --repo does.
    Cache/WORKFLOWS.md describes the three workflows in full.

    The upload commands (put, put!, put-staged) and their flags and variables
    are internal to mathlib CI. An upload goes under MATHLIB_CACHE_PUT_URL:
    flat (f/), or with --dev-cache the developer cache's repo-namespaced
    layout (f/REPO/ with --repo; f/REPO/SHA/ and its marker with --scope).
    --container=NAME stands for both, the container's Azure base and its
    form; the variable overrides the URL. To operate an
    external cache, stage the artifacts, upload the staging directory under
    your endpoint's f/ path with any storage client, and serve it to readers
    via MATHLIB_CACHE_GET_URL.

ENVIRONMENT VARIABLES
    MATHLIB_CACHE_DIR       Local cache directory (default: ~/.cache/mathlib)
    MATHLIB_CACHE_DEBUG_USE_LEGACY
                            Set to 1 or true to read from the Azure storage
                            account instead of the cache endpoints.
                            For troubleshooting only.
    MATHLIB_CACHE_GET_URL   Download from this single URL as a flat namespace.
                            Allows third parties to use their own cache endpoint.
                            An empty value means unset."

/-- The roots the module arguments of `p` name, `Mathlib` when there are none,
and the hash memo over them. -/
def hashMemoFor (p : Parsed) : CacheM (Std.HashMap Lean.Name FilePath × HashMemo) := do
  let mut roots ← parseModuleSpecs (p.variableArgsAs! String).toList
  if roots.isEmpty then
    -- TODO: could change this to the default-target of a downstream project
    let mod := `Mathlib
    roots := roots.insert mod (← Lean.findLean (← read).srcSearchPath mod)
  return (roots, ← getHashMemo roots)

/-- `pack` the files of `hashMap` into the local cache; the file names. -/
def pack (hashMap : ModuleHashMap) (overwrite verbose unpackedOnly : Bool) :
    CacheM (Array String) := do
  packCache hashMap overwrite verbose unpackedOnly (← getGitCommitHash)

/-- `get`, `get!` (`force`) and `get-` (no `decompress`): resolve the repo
once, decide the workflow, and hand it the read. -/
def runGet (force decompress : Bool) (p : Parsed) : IO UInt32 := CacheM.run do
  let repoExplicit? := CommonFlag.repoOf p
  let getURL? := normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_GET_URL")
  let (roots, hashMemo) ← hashMemoFor p
  let hashMap ← if p.variableArgs.isEmpty then pure hashMemo.hashMap
    else hashMemo.filterByRootModules roots.keys
  let parallel ← validateCurl
  let mathlibDepPath := (← read).mathlibDepPath
  let isMathlibRoot ← IO.isMathlibRoot
  let (detectedRepo?, repo) ← resolveRepo repoExplicit? mathlibDepPath isMathlibRoot
  let workflow := Workflow.forRead repo getURL? (← Workflow.chainReadRequested p)
  workflow.get p
    { repoExplicit?, repo, detectedRepo?, getURL?,
      -- The workflows' git probes run in the mathlib checkout: the dependency
      -- checkout when Mathlib is a dependency.
      mathlibCwd := if isMathlibRoot then "." else mathlibDepPath }
    { hashMap, forceDownload := force, decompress, parallel }
  return 0

/-- `pack` and `pack!` (`overwrite`). -/
def runPack (overwrite : Bool) (p : Parsed) : IO UInt32 := CacheM.run do
  let (_, hashMemo) ← hashMemoFor p
  discard <| pack hashMemo.hashMap overwrite (verbose := false) (unpackedOnly := false)
  return 0

/-- `unpack` and `unpack!` (`force`). -/
def runUnpack (force : Bool) (p : Parsed) : IO UInt32 := CacheM.run do
  let (_, hashMemo) ← hashMemoFor p
  unpackCache hashMemo.hashMap force
  return 0

/-- `clean`: delete the files the build does not link; `clean!` (`all`):
delete every file of the local cache. -/
def runClean (all : Bool) (p : Parsed) : IO UInt32 := CacheM.run do
  if all then
    cleanCache
  else
    let (_, hashMemo) ← hashMemoFor p
    cleanCache <| hashMemo.hashMap.fold (init := .empty) fun acc _ hash =>
      acc.insert <| CACHEDIR / hash.asLTar
  return 0

/-- `lookup`. -/
def runLookup (p : Parsed) : IO UInt32 := CacheM.run do
  let (roots, hashMemo) ← hashMemoFor p
  lookup hashMemo.hashMap roots.keys
  return 0

/-- The decision of a `put`: the upload and the URL it goes under, from the
flags, `MATHLIB_CACHE_PUT_URL` (an empty value means unset), and the scope
(`Upload.decide`). A mismatch fails here, before any packing. The upload is
printed, as `get` prints its workflow. -/
def uploadOf (p : Parsed) : IO (Upload × String) := do
  let options : Upload.Options := {
    devCache := p.hasFlag Upload.devCacheFlag.longName
    container? := (p.flag? Upload.containerFlag.longName).map (·.as! Container)
    repo? := CommonFlag.repoOf p
    scope? := ← Scope.parse p
    putURL? := normalizeBaseURL (← IO.getEnv "MATHLIB_CACHE_PUT_URL") }
  match Upload.decide options with
  | .ok (upload, url) =>
    IO.println s!"Cache upload: {upload.name}"
    pure (upload, url)
  | .error msg =>
    IO.eprintln msg
    IO.Process.exit 1

/-- `put` and `put!` (`overwrite`): `pack`, then upload. The hash memo scopes
the file list to what this checkout's build links, so nothing else in the
shared per-user cache directory is uploaded. -/
def runPut (overwrite : Bool) (p : Parsed) : IO UInt32 := CacheM.run do
  let (upload, url) ← uploadOf p
  let (_, hashMemo) ← hashMemoFor p
  uploadFiles upload url (CommonFlag.backendOf p) IO.CACHEDIR
    (getFileNames := pack hashMemo.hashMap overwrite (verbose := true) (unpackedOnly := false))
    overwrite
  return 0

/-- `put-staged`: upload the `.ltar` files of the staging directory. It needs
no hash memo. -/
def runPutStaged (p : Parsed) : IO UInt32 := do
  let some stagingDir := CommonFlag.stagingDirOf p | return 1
  if !(← stagingDir.isDir) then
    IO.eprintln "--staging-dir must be a directory"
    return 1
  let (upload, url) ← uploadOf p
  uploadFiles upload url (CommonFlag.backendOf p) stagingDir (overwrite := false)
    (getFileNames := do
      return (← getFilesWithExtension stagingDir "ltar").map (·.fileName.get!))
  return 0

/-- `stage` (the files not yet packed, `unpackedOnly`) and `stage!` (every
linked file). -/
def runStage (unpackedOnly : Bool) (p : Parsed) : IO UInt32 := CacheM.run do
  let some stagingDir := CommonFlag.stagingDirOf p | return 1
  let (_, hashMemo) ← hashMemoFor p
  stageFiles stagingDir
    (← pack hashMemo.hashMap (overwrite := false) (verbose := true) unpackedOnly)
  return 0

/-- `unstage` and `unstage!` (`overwrite`). -/
def runUnstage (overwrite : Bool) (p : Parsed) : IO UInt32 := do
  let some stagingDir := CommonFlag.stagingDirOf p | return 1
  unstageFiles stagingDir overwrite
  return 0

/-- `query [REF]`, a developer-cache command. It needs no hash memo: git and
one HTTP probe. -/
def runQuery (p : Parsed) : IO UInt32 := do
  let refs := p.variableArgsAs! String
  if refs.size > 1 then
    IO.eprintln "Usage: cache query [REF]"
    return 1
  let repo ← Developer.resolveQueryRepo (CommonFlag.repoOf p) (← IO.isMathlibRoot)
  Developer.query repo refs[0]?
  return 0

/-- A `get` command: the flags of every workflow, and modules. -/
def getCmd (name description : String) (force decompress : Bool) : Cmd :=
  .mk name none description
    (flags := #[CommonFlag.repo] ++ Workflow.flags)
    (variableArg? := some modulesArg)
    (run := runGet force decompress)

/-- The flags of an upload: the developer-cache switch, the well-known
container, the fork it is for, the backend, and the per-commit scope. -/
def uploadFlags : Array Cli.Flag :=
  #[Upload.devCacheFlag, Upload.containerFlag, CommonFlag.repo, CommonFlag.backend, Scope.flag]

/-- A `put` command: the upload flags, and modules. -/
def putCmd (name description : String) (overwrite : Bool) : Cmd :=
  .mk name none description
    (flags := uploadFlags)
    (variableArg? := some modulesArg)
    (run := runPut overwrite)

/-- A command with modules and no flags. -/
def modulesCmd (name description : String) (run : Parsed → IO UInt32) : Cmd :=
  .mk name none description (variableArg? := some modulesArg) (run := run)

/-- A command with neither flags nor arguments. -/
def plainCmd (name description : String) (run : Parsed → IO UInt32) : Cmd :=
  .mk name none description (run := run)

/-- A command that requires `--staging-dir`. -/
def stagingCmd (name description : String) (flags : Array Cli.Flag) (modules : Bool)
    (run : Parsed → IO UInt32) : Cmd :=
  .mk name none description
    (flags := #[CommonFlag.stagingDir] ++ flags)
    (variableArg? := if modules then some modulesArg else none)
    (run := run)
    (extension? := some (Cli.require! #[CommonFlag.stagingDir.longName]))

/-- The `cache` command and its subcommands. Without a subcommand it prints
the help. -/
def cache : Cmd :=
  .mk "cache" none "Mathlib's build cache: the .olean files of a build, downloaded instead of \
      rebuilt."
    (furtherInformation? := some furtherInformation)
    (run := fun p => do p.printHelp; return 0)
    (subCmds := #[
      getCmd "get" "Download the linked files missing on the local cache and decompress them."
        (force := false) (decompress := true),
      getCmd "get!" "Download all the linked files and decompress them."
        (force := true) (decompress := true),
      getCmd "get-" "Download the linked files missing on the local cache without decompressing."
        (force := false) (decompress := false),
      modulesCmd "pack" "Compress the build files not yet in the local cache." (runPack false),
      modulesCmd "pack!" "Compress the build files into the local cache (no skipping)."
        (runPack true),
      modulesCmd "unpack" "Decompress the linked, already downloaded files." (runUnpack false),
      modulesCmd "unpack!" "Decompress the linked, already downloaded files (no skipping)."
        (runUnpack true),
      modulesCmd "clean" "Delete the files of the local cache the build does not link."
        (runClean false),
      plainCmd "clean!" "Delete every file of the local cache." (runClean true),
      modulesCmd "lookup" "Show information about the cache files of the given Lean files."
        runLookup,
      .mk "query" none "Without REF: find the most recent cached commit on this branch. With REF \
          (HEAD, a SHA): exit 0 if that commit is cached, 1 if not."
        (flags := #[CommonFlag.repo])
        (variableArg? := some { name := "ref", description := "A git ref.", type := String })
        (run := runQuery),
      putCmd "put" "pack, then upload the files this build links (mathlib CI)."
        (overwrite := false),
      putCmd "put!" "pack, then upload the files this build links, overwriting (mathlib CI)."
        (overwrite := true),
      stagingCmd "put-staged" "Upload the .ltar files of the staging directory (mathlib CI)."
        (flags := uploadFlags) (modules := false) runPutStaged,
      stagingCmd "stage" "Copy the files not yet packed to the staging directory."
        (flags := #[]) (modules := true) (runStage true),
      stagingCmd "stage!" "Copy every linked cache file to the staging directory."
        (flags := #[]) (modules := true) (runStage false),
      stagingCmd "unstage" "Copy the .ltar files of the staging directory into the local cache."
        (flags := #[]) (modules := false) (runUnstage false),
      stagingCmd "unstage!" "Copy the .ltar files of the staging directory into the local cache, \
          overwriting."
        (flags := #[]) (modules := false) (runUnstage true)])

/-- Leading flags moved after the command: `cache --repo=X get` reads as
`cache get --repo=X`. CI names the repo before the command. Arguments that
are all flags, or that start with a command, are returned as they are. -/
def normalizeArgs (args : List String) : List String :=
  let (flags, rest) := args.span (·.startsWith "-")
  match rest with
  | cmd :: tail => cmd :: (flags ++ tail)
  | [] => flags

/-- The entry point: the legacy switch, then the command tree. A first
argument that names no command is reported as such. -/
def main (args : List String) : IO UInt32 := do
  -- Resolve the legacy switch once, before anything builds a read URL.
  useLegacy.set (← getEnvFlag "MATHLIB_CACHE_DEBUG_USE_LEGACY" (ifUnset := false))
  let args := normalizeArgs args
  if let some cmd := args.head? then
    if !cmd.startsWith "-" && !cache.hasSubCmd cmd then
      cache.printError s!"Unknown command `{cmd}`."
      return 1
  cache.validate args

end Cache.Commands
