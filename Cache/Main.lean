/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.Requests

def help : String := "Mathlib4 caching CLI
Usage: cache [COMMAND]

Commands:
  # No priviledge required
  get  [ARGS]  Download linked files missing on the local cache and decompress
  get! [ARGS]  Download all linked files and decompress
  mk           Compress non-compressed build files into the local cache
  mk!          Compress build files into the local cache (no skipping)
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

'get' and 'get!' can process list of paths containing at most one wildcard each,
allowing the user to be more specific about what should be downloaded. Example:

$ lake exe cache get Mathlib/Algebra/Field/* Mathlib/Data *Conjugate.lean

Will download the cache for:
* Everything that starts with 'Mathlib/Algebra/Field/'
* Everything that starts with 'Mathlib/Data'
* Everything that ends with 'Conjugate.lean'"

open Cache IO Hashing Requests in
def main (args : List String) : IO Unit := do
  if !(← validateCurl) then return
  let hashMemo ← getHashMemo
  let hashMap := hashMemo.hashMap
  match args with
  | "get"  :: args => getFiles (← hashMemo.filterByPatterns args) false
  | "get!" :: args => getFiles (← hashMemo.filterByPatterns args) true
  | ["mk"] => discard $ mkCache hashMap false
  | ["mk!"] => discard $ mkCache hashMap true
  | ["unpack"] => unpackCache hashMap
  | ["clean"] =>
    cleanCache $ hashMap.fold (fun acc _ hash => acc.insert $ CACHEDIR / hash.asTarGz) .empty
  | ["clean!"] => cleanCache
  | ["put"] => putFiles (← mkCache hashMap false) false (← getToken)
  | ["put!"] => putFiles (← mkCache hashMap false) true (← getToken)
  | ["commit"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap false (← getToken)
  | ["commit!"] =>
    if !(← isGitStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap true (← getToken)
  | ["collect"] => IO.println "TODO"
  | _ => println help
