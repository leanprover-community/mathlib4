/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.Requests

def help : String := "Caching CLI
Usage: cache [COMMAND]

Commands:
  # No priviledge required
  get  [ARGS]  Download linked files missing on the local cache and decompress
  get! [ARGS]  Download all linked files and decompress
  pack         Compress non-compressed build files into the local cache
  pack!        Compress build files into the local cache (no skipping)
  unpack       Decompress linked already downloaded files
  clean        Delete non-linked files
  clean!       Delete everything on the local cache

  # Privilege required
  put          Run 'mk' then upload linked files missing on the server
  put!         Run 'mk' then upload all linked files
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

open System (FilePath) in
/-- Note that this normalizes the path strings, which is needed when running from a unix shell
(which uses `/` in paths) on windows (which uses `\` in paths) as otherwise our filename keys won't
match. -/
def toPaths (args : List String) : List FilePath :=
  args.map (FilePath.mk · |>.normalize)

def curlArgs : List String :=
  ["get", "get!", "put", "put!", "commit", "commit!"]

open Cache IO Hashing Requests in
def main (args : List String) : IO Unit := do
  if !(← Config.check) then IO.println "Cache config file not found"; return
  let config ← match ← Config.load with
    | .ok config => pure config
    | .error err => IO.println err; return
  if curlArgs.contains (args.headD "") && !(← validateCurl) then return
  let hashMemo ← getHashMemo config
  let hashMap := hashMemo.hashMap
  let url := config.url
  match args with
  | ["get"] => getFiles config hashMap false
  | ["get!"] => getFiles config hashMap true
  | "get"  :: args => getFiles config (← hashMemo.filterByFilePaths (toPaths args)) false
  | "get!" :: args => getFiles config (← hashMemo.filterByFilePaths (toPaths args)) true
  | ["pack"] => discard $ packCache config.pkgDirs hashMap false
  | ["pack!"] => discard $ packCache config.pkgDirs hashMap true
  | ["unpack"] => unpackCache config hashMap
  | ["clean"] =>
    cleanCache $ hashMap.fold (fun acc _ hash => acc.insert $ CACHEDIR / hash.asTarGz) .empty
  | ["clean!"] => cleanCache
  | ["put"] =>
    putFiles url (← packCache config.pkgDirs hashMap false) false (← getToken config.tokenEnvVar)
  | ["put!"] =>
    putFiles url (← packCache config.pkgDirs hashMap false) true (← getToken config.tokenEnvVar)
  | ["commit"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit url hashMap false (← getToken config.tokenEnvVar)
  | ["commit!"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit url hashMap true (← getToken config.tokenEnvVar)
  | ["collect"] => IO.println "TODO"
  | _ => println help
