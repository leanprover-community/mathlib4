/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.Requests

def help : String := "Mathlib4 caching CLI
Usage: cache [COMMAND]

Commands:
  # No privilege required
  get  [ARGS]  Download linked files missing on the local cache and decompress
  get! [ARGS]  Download all linked files and decompress
  get- [ARGS]  Download linked files missing to the local cache, but do no compress
  pack         Compress non-compressed build files into the local cache
  pack!        Compress build files into the local cache (no skipping)
  unpack       Decompress linked already downloaded files
  unpack!      Decompress linked already downloaded files (no skipping)
  clean        Delete non-linked files
  clean!       Delete everything on the local cache
  lookup       Show information about cache files for the given lean files

  # Privilege required
  put          Run 'mk' then upload linked files missing on the server
  put!         Run 'mk' then upload all linked files
  put-unpacked 'put' only files not already 'pack'ed; intended for CI use
  commit       Write a commit on the server
  commit!      Overwrite a commit on the server
  collect      TODO

* Linked files refer to local cache files with corresponding Lean sources
* Commands ending with '!' should be used manually, when hot-fixes are needed

# The arguments for 'get' and 'get!'

'get' and 'get!' can process list of paths, allowing the user to be more
specific about what should be downloaded. For example, with automatic glob
expansion in shell, one can call:

$ lake exe cache get Mathlib/Algebra/Field/*.lean Mathlib/Data/*.lean

Which will download the cache for:
* Every Lean file inside 'Mathlib/Algebra/Field/'
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

def curlArgs : List String :=
  ["get", "get!", "get-", "put", "put!", "put-unpacked", "commit", "commit!"]

def leanTarArgs : List String :=
  ["get", "get!", "pack", "pack!", "unpack", "lookup"]

open Cache IO Hashing Requests System in
def main (args : List String) : IO Unit := do
  if Lean.versionString == "4.8.0-rc1" && Lean.githash == "b470eb522bfd68ca96938c23f6a1bce79da8a99f" then do
    println "Unfortunately, you have a broken Lean v4.8.0-rc1 installation."
    println "Please run `elan toolchain uninstall leanprover/lean4:v4.8.0-rc1` and try again."
    Process.exit 1
  -- We pass any following arguments to `getHashMemo`,
  -- so we can use the cache on `Archive` or `Counterexamples`.
  let extraRoots := match args with
  | [] => #[]
  | _ :: t => t.toArray.map FilePath.mk
  if args.isEmpty then
    println help
    Process.exit 0
  CacheM.run do
  let hashMemo ← getHashMemo extraRoots
  let hashMap := hashMemo.hashMap
  let goodCurl ← pure !curlArgs.contains (args.headD "") <||> validateCurl
  if leanTarArgs.contains (args.headD "") then validateLeanTar
  let get (args : List String) (force := false) (decompress := true) := do
    let hashMap ← if args.isEmpty then pure hashMap else hashMemo.filterByFilePaths (toPaths args)
    getFiles hashMap force force goodCurl decompress
  let pack (overwrite verbose unpackedOnly := false) := do
    packCache hashMap overwrite verbose unpackedOnly (← getGitCommitHash)
  let put (overwrite unpackedOnly := false) := do
    putFiles (← pack overwrite (verbose := true) unpackedOnly) overwrite (← getToken)
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
  | "lookup" :: args => lookup hashMap (toPaths args)
  | _ => println help
