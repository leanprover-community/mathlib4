import Cache.Requests

open Cache

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

def main (args : List String) : IO UInt32 := do
  let hashMap ← Hashing.getHashes
  match args with
  | ["get"] =>
    let localCacheSet ← IO.getLocalCacheSet
    Requests.getFiles $ hashMap.filter fun _ hash => !localCacheSet.contains hash.asTarGz
  | ["get!"] => Requests.getFiles hashMap
  | ["mk"] => discard $ IO.mkCache hashMap
  | ["set"] => IO.setCache hashMap
  | ["clear"] =>
    let except := hashMap.fold (fun acc _ hash => acc.insert $ IO.CACHEDIR / hash.asTarGz) .empty
    IO.clearCache except
  | ["clear!"] => IO.clearCache
  | ["put"] => Requests.putFiles (← IO.mkCache hashMap) false (← IO.getToken)
  | ["put!"] => Requests.putFiles (← IO.mkCache hashMap) true (← IO.getToken)
  | ["persist"] => -- TODO
    pure ()
  | ["collect"] => -- WARNING: CURRENTLY DELETES ALL FILES FROM THE SERVER
    Requests.collectCache (← IO.getToken)
  | _ => IO.println help
  return 0
