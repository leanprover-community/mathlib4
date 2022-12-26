import Cache.Requests

open Cache

def help : String := "Mathlib4 caching CLI
Usage: cache [COMMAND]

Commands:
  put   Compress and upload linked files that are missing on the server
  put!  Compress and upload all linked files
  get   Download and decompress linked files that are missing on the local cache
  get!  Download and decompress all linked files
  set   Decompress linked files
  clr   Delete non-linked files
  clr!  Delete everything on the local cache

* Linked files refer to local cache files with corresponding Lean sources"

def main : List String → IO UInt32
  | ["put"]  => Requests.putCache
  | ["put!"] => Requests.putCache!
  | ["get"]  => Requests.getCache
  | ["get!"] => Requests.getCache!
  | ["set"]  => do IO.setCache (← Hashing.getHashes)
  | ["clr"]  => do
    let hashMap ← Hashing.getHashes
    let except := hashMap.fold (fun acc _ hash => acc.insert s!"{IO.CACHEDIR}/{hash}.zip") default
    IO.clrCache except
    return 0
  | ["clr!"] => do IO.clrCache; return 0
  | _ => do
    IO.println help
    return 0
