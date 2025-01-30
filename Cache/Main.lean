/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.Requests

/-!

## Technical notes

It looks like the Lean search-path `addSearchPathFromEnv {}` cannot be used
because we might call `lake exe cache` before files are built.
-/


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

# The arguments for 'get', 'get!' and 'get-'

'get', 'get!' and 'get-' can process a list of module names, allowing the user to be more
specific about what should be downloaded. For example, one can call:

$ lake exe cache get Mathlib.Algebra.Field.Basic Mathlib.Data

Which will download the cache for:
* The file 'Mathlib/Algebra/Field/Basic.lean'
* Every Lean file inside 'Mathlib/Data/'
* Everything that's needed for the above"

open Lean System in
/-- Note that this normalizes the path strings, which is needed when running from a unix shell
(which uses `/` in paths) on windows (which uses `\` in paths) as otherwise our filename keys won't
match. -/
def toPaths (args : List String) : List FilePath :=
  args.map fun arg =>
    if arg.endsWith ".lean" then
      FilePath.mk arg |>.normalize
    else
      mkFilePath (arg.toName.components.map Name.toString) |>.withExtension "lean"

/-- Commands which (potentially) call `curl` for downloading files -/
def curlArgs : List String :=
  ["get", "get!", "get-", "put", "put!", "put-unpacked", "commit", "commit!"]

/-- Commands which (potentially) call `leantar` for decompressing downloaded files -/
def leanTarArgs : List String :=
  ["get", "get!", "pack", "pack!", "unpack", "lookup"]

open Lean System in

open Cache IO Hashing Requests System in
def main (args : List String) : IO Unit := do
  if Lean.versionString == "4.8.0-rc1" && Lean.githash == "b470eb522bfd68ca96938c23f6a1bce79da8a99f" then do
    println "Unfortunately, you have a broken Lean v4.8.0-rc1 installation."
    println "Please run `elan toolchain uninstall leanprover/lean4:v4.8.0-rc1` and try again."
    Process.exit 1
  CacheM.run do
  -- We pass any following arguments to `getHashMemo`,
  -- so we can use the cache on `Archive` or `Counterexamples`.
  let mut extraRoots : Std.HashMap Lean.Name FilePath ← parseArgs args
  if extraRoots.isEmpty then do
    -- No arguments means to start from `Mathlib.lean`
    -- TODO: could change this to the default-target of a downstream project
    let mod := `Mathlib
    let sp := (← read).searchPath
    let sourceFile ← Lean.findLean sp mod
    extraRoots := Std.HashMap.empty.insert mod sourceFile

  if args.isEmpty then
    println help
    Process.exit 0
  let hashMemo ← getHashMemo extraRoots
  let hashMap := hashMemo.hashMap
  let pathMap := hashMemo.pathMap
  let goodCurl ← pure !curlArgs.contains (args.headD "") <||> validateCurl
  if leanTarArgs.contains (args.headD "") then validateLeanTar
  let get (force := false) (decompress := true) := do
    getFiles hashMap pathMap force goodCurl decompress
  let pack (overwrite verbose unpackedOnly := false) := do
    packCache hashMap pathMap overwrite verbose unpackedOnly (← getGitCommitHash)
  let put (overwrite unpackedOnly := false) := do
    putFiles (← pack overwrite (verbose := true) unpackedOnly) overwrite (← getToken)
  match args with
  | "get"  :: _ => get
  | "get!" :: _ => get (force := true)
  | "get-" :: _ => get (decompress := false)
  | ["pack"] => discard <| pack
  | ["pack!"] => discard <| pack (overwrite := true)
  | ["unpack"] => unpackCache hashMap pathMap false
  | ["unpack!"] => unpackCache hashMap pathMap true
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
  | "lookup" :: args => lookup hashMap (args.map String.toName)
  | _ => println help
