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
  get       Download and decompress linked files missing on the local cache
  get!      Download and decompress all linked files
  mk        Compress non-compressed build files into the local cache
  mk!       Compress build files into the local cache (no skipping)
  set       Decompress linked files
  clear     Delete non-linked files
  clear!    Delete everything on the local cache

  # Privilege required
  put       Run 'mk' then upload linked files missing on the server
  put!      Run 'mk' then upload all linked files
  commit    Write a commit on the server
  commit!   (Over)write a commit on the server
  collect   TODO

* Linked files refer to local cache files with corresponding Lean sources
* Commands ending with '!' should be used manually, when hot-fixes are needed"

open Cache IO Hashing Requests in
def main (args : List String) : IO Unit := do
  let hashMap  ← getHashes
  match args with
  | ["get"] => getFiles (hashMap.filter (← getLocalCacheSet) false)
  | ["get!"] => getFiles hashMap
  | ["mk"] => discard $ mkCache hashMap false
  | ["mk!"] => discard $ mkCache hashMap true
  | ["set"] => setCache hashMap
  | ["clear"] =>
    clearCache $ hashMap.fold (fun acc _ hash => acc.insert $ CACHEDIR / hash.asTarGz) .empty
  | ["clear!"] => clearCache
  | ["put"] => putFiles (← mkCache hashMap false) false (← getToken)
  | ["put!"] => putFiles (← mkCache hashMap false) true (← getToken)
  | ["commit"] =>
    if !(← isStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap false (← getToken)
  | ["commit!"] =>
    if !(← isStatusClean) then IO.println "Please commit your changes first" return else
    commit hashMap true (← getToken)
  | ["collect"] => IO.println "TODO"
  | _ => println help
