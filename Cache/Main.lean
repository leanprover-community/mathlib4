/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster
-/

import Cache.Requests

def help : String := "Mathlib4 caching CLI
Usage: cache [COMMAND]

Commands:
  # No privilege required
  get  [ARGS]   Download linked files missing on the local cache and decompress
  get! [ARGS]   Download all linked files and decompress
  get- [ARGS]   Download linked files missing to the local cache, but do not decompress
  pack          Compress non-compressed build files into the local cache
  pack!         Compress build files into the local cache (no skipping)
  unpack        Decompress linked already downloaded files
  unpack!       Decompress linked already downloaded files (no skipping)
  clean         Delete non-linked files
  clean!        Delete everything on the local cache
  lookup [ARGS] Show information about cache files for the given lean files

  # Privilege required
  put          Run 'mk' then upload linked files missing on the server
  put!         Run 'mk' then upload all linked files
  put-unpacked 'put' only files not already 'pack'ed; intended for CI use
  commit       Write a commit on the server
  commit!      Overwrite a commit on the server
  collect      TODO

* Linked files refer to local cache files with corresponding Lean sources
* Commands ending with '!' should be used manually, when hot-fixes are needed

# The arguments for 'get', 'get!', 'get-' and 'lookup'

'get', 'get!', 'get-' and 'lookup' can process a list of module names or file names.

'get [ARGS]' will only get the cache for the specified Lean files and all files imported by one.

Valid arguments are:

* Module names like 'Mathlib.Init'
* File names like 'Mathlib/Init.lean'
* Folder names like 'Mathlib/Data/' (find all Lean files inside `Mathlib/Data/`)
* With bash's automatic glob expansion one can also write things like
  'Mathlib/**/Order/*.lean'.
"

/-- Commands which (potentially) call `curl` for downloading files -/
def curlArgs : List String :=
  ["get", "get!", "get-", "put", "put!", "put-unpacked", "commit", "commit!"]

/-- Commands which (potentially) call `leantar` for decompressing downloaded files -/
def leanTarArgs : List String :=
  ["get", "get!", "pack", "pack!", "unpack", "lookup"]

/-- Parses an optional `--repo` option. -/
def parseRepo (args : List String) : IO (Option String × List String) := do
  if let arg :: args := args then
    if arg.startsWith "--" then
      if let some repo := arg.dropPrefix? "--repo=" then
        return (some repo.toString, args)
      else
        throw <| IO.userError s!"unknown option: {arg}"
  return (none, args)

open Cache IO Hashing Requests System in
def main (args : List String) : IO Unit := do
  if Lean.versionString == "4.8.0-rc1" && Lean.githash == "b470eb522bfd68ca96938c23f6a1bce79da8a99f" then do
    println "Unfortunately, you have a broken Lean v4.8.0-rc1 installation."
    println "Please run `elan toolchain uninstall leanprover/lean4:v4.8.0-rc1` and try again."
    Process.exit 1
  if args.isEmpty then
    println help
    Process.exit 0
  CacheM.run do

  let (repo?, args) ← parseRepo args
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
  if leanTarArgs.contains (args.headD "") then validateLeanTar
  let get (args : List String) (force := false) (decompress := true) := do
    let hashMap ← if args.isEmpty then pure hashMap else hashMemo.filterByRootModules roots.keys
    getFiles repo? hashMap force force goodCurl decompress
  let pack (overwrite verbose unpackedOnly := false) := do
    packCache hashMap overwrite verbose unpackedOnly (← getGitCommitHash)
  let put (overwrite unpackedOnly := false) := do
    let repo := repo?.getD MATHLIBREPO
    putFiles repo (← pack overwrite (verbose := true) unpackedOnly) overwrite (← getToken)
  match args with
  | "get"  :: args => get args
  | "get!" :: args => get args (force := true)
  | "get-" :: args => get args (decompress := false)
  | ["pack"] => discard <| pack
  | ["pack!"] => discard <| pack (overwrite := true)
  | ["unpack"] => unpackCache hashMap false
  | ["unpack!"] => unpackCache hashMap true
  | ["clean"] =>
    cleanCache <| hashMap.fold (fun acc _ hash => acc.insert <| CACHEDIR / hash.asLTar) .empty
  | ["clean!"] => cleanCache
  -- We allow arguments for `put*` so they can be added to the `roots`.
  | "put" :: _ => put
  | "put!" :: _ => put (overwrite := true)
  | "put-unpacked" :: _ => put (unpackedOnly := true)
  | ["commit"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap false (← getToken)
  | ["commit!"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap true (← getToken)
  | ["collect"] => IO.println "TODO"
  | "lookup" :: _ => lookup hashMap roots.keys
  | _ => println help
