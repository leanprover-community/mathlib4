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

# The arguments for 'get', 'get!', 'get-'

'get', 'get!', 'get-' can process a list of module names or file names.
'get [ARGS]' will only get the cache for the specified Lean files and all files imported by one.

Valid arguments are:

* Module names like 'Mathlib.Init'
* Pseudo-module-names like 'Mathlib.Data' (find all Lean files inside `Mathlib/Data/`)
* File names like 'Mathlib/Init.lean'
* Folder names like 'Mathlib/Data/' (find all Lean files inside `Mathlib/Data/`)
* With bash's automatic glob expansion one can also write things like
  'Mathlib/**/Order/*.lean'.

'lookup' takes the same arguments as 'get' but prints information about the corresponding
hash files for debugging purposes.
"

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
  if args.isEmpty then
    println help
    Process.exit 0
  -- Hashing everything imported transitively by one of the root modules
  let mut roots : Std.HashMap Lean.Name FilePath ← parseArgs args
  if roots.isEmpty then do
    -- No arguments means to start from `Mathlib.lean`
    -- TODO: could change this to the default-target of a downstream project
    let mod := `Mathlib
    let sp := (← read).searchPath
    let sourceFile ← Lean.findLean sp mod
    roots := Std.HashMap.empty.insert mod sourceFile
  let hashMemo ← getHashMemo roots

  let goodCurl ← pure !curlArgs.contains (args.headD "") <||> validateCurl
  if leanTarArgs.contains (args.headD "") then validateLeanTar
  let get (force := false) (decompress := true) := do
    getFiles hashMemo.hashMap hashMemo.pathMap force force goodCurl decompress
  let pack (overwrite verbose unpackedOnly := false) := do
    packCache hashMemo.hashMap hashMemo.pathMap overwrite verbose unpackedOnly (← getGitCommitHash)
  let put (overwrite unpackedOnly := false) := do
    putFiles (← pack overwrite (verbose := true) unpackedOnly) overwrite (← getToken)
  match args with
  | "get"  :: _ => get
  | "get!" :: _ => get (force := true)
  | "get-" :: _ => get (decompress := false)
  | ["pack"] => discard <| pack
  | ["pack!"] => discard <| pack (overwrite := true)
  | ["unpack"] => unpackCache hashMemo.hashMap hashMemo.pathMap false
  | ["unpack!"] => unpackCache hashMemo.hashMap hashMemo.pathMap true
  | ["clean"] =>
    cleanCache <| hashMemo.hashMap.fold (fun acc _ hash => acc.insert <| CACHEDIR / hash.asLTar) .empty
  | ["clean!"] => cleanCache
  -- We allow arguments for `put*` so they can be added to the `roots`.
  | "put" :: _ => put
  | "put!" :: _ => put (overwrite := true)
  | "put-unpacked" :: _ => put (unpackedOnly := true)
  | ["commit"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMemo.hashMap false (← getToken)
  | ["commit!"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMemo.hashMap true (← getToken)
  | ["collect"] => IO.println "TODO"
  | "lookup" :: _ => lookup hashMemo.hashMap (roots.keys)
  | _ => println help
