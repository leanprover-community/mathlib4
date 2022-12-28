import Cache.Requests

def help : String := "Mathlib4 caching CLI
Usage: cache [COMMAND]

Commands:
  # No priviledge required
  get       Download and decompress linked files missing on the local cache
  get!      Download and decompress all linked files
  mk        Compress build files into the local cache
  set       Decompress linked files
  clear     Delete non-linked files
  clear!    Delete everything on the local cache

  # Priviledge required
  put       Call 'mk' and then upload linked files missing on the server
  put!      Call 'mk' and then upload all linked files
  persist   TODO
  collect   TODO

* Linked files refer to local cache files with corresponding Lean sources"

open Cache IO Hashing Requests in
def main (args : List String) : IO Unit := do
  let hashMap ← getHashes
  match args with
  | ["get"] =>
    let localCacheSet ← getLocalCacheSet
    getFiles $ hashMap.filter fun _ hash => !localCacheSet.contains hash.asTarGz
  | ["get!"] => getFiles hashMap
  | ["mk"] => discard $ mkCache hashMap
  | ["set"] => setCache hashMap
  | ["clear"] =>
    clearCache $ hashMap.fold (fun acc _ hash => acc.insert $ CACHEDIR / hash.asTarGz) .empty
  | ["clear!"] => clearCache
  | ["put"] => putFiles (← mkCache hashMap) false (← getToken)
  | ["put!"] => putFiles (← mkCache hashMap) true (← getToken)
  | ["persist"] => pure () -- TODO
  | ["collect"] => collectCache (← getToken) -- WARNING: CURRENTLY DELETES ALL FILES FROM THE SERVER
  | ["dbg"] => println $ hashMap.size
  | _ => println help
