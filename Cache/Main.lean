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
  ["get", "get!", "get-", "put", "put!", "commit", "commit!"]

def leanTarArgs : List String :=
  ["get", "get!", "pack", "pack!", "unpack"]

open Cache IO Hashing Requests in
def main (args : List String) : IO Unit := do
  let hashMemo ← getHashMemo
  let hashMap := hashMemo.hashMap
  let goodCurl ← pure !curlArgs.contains (args.headD "") <||> validateCurl
  if leanTarArgs.contains (args.headD "") then validateLeanTar
  match args with
  | ["get"] => getFiles hashMap false goodCurl true
  | ["get!"] => getFiles hashMap true goodCurl true
  | ["get-"] => getFiles hashMap false goodCurl false
  | "get"  :: args => getFiles (← hashMemo.filterByFilePaths (toPaths args)) false goodCurl true
  | "get!" :: args => getFiles (← hashMemo.filterByFilePaths (toPaths args)) true goodCurl true
  | "get-"  :: args => getFiles (← hashMemo.filterByFilePaths (toPaths args)) false goodCurl false
  | ["pack"] => discard $ packCache hashMap false
  | ["pack!"] => discard $ packCache hashMap true
  | ["unpack"] => unpackCache hashMap
  | ["clean"] =>
    cleanCache $ hashMap.fold (fun acc _ hash => acc.insert $ CACHEDIR / hash.asLTar) .empty
  | ["clean!"] => cleanCache
  | ["put"] => putFiles (← packCache hashMap false) false (← getToken)
  | ["put!"] => putFiles (← packCache hashMap false) true (← getToken)
  | ["commit"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap false (← getToken)
  | ["commit!"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap true (← getToken)
  | ["collect"] => IO.println "TODO"
  | _ => println help
