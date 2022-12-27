import Cache.Requests

open Cache

def help : String := "Mathlib4 caching CLI
Usage: cache [COMMAND]

Commands:
  zip   Compress build files into the local cache
  put   Call 'zip' and then upload linked files missing on the server
  put!  Call 'zip' and then upload all linked files
  get   Download and decompress linked files missing on the local cache
  get!  Download and decompress all linked files
  set   Decompress linked files
  clr   Delete non-linked files
  clr!  Delete everything on the local cache

* Linked files refer to local cache files with corresponding Lean sources
* Uploading files to Azure requires a token written in a text file called
  'azure.token', placed in the root directory of the Mathlib repo"

def main : List String → IO UInt32
  | ["zip" ] => do discard $ IO.zipCache $ ← Hashing.getHashes; return 0
  | ["put" ] => Requests.putCache
  | ["put!"] => Requests.putCache!
  | ["get" ] => Requests.getCache
  | ["get!"] => Requests.getCache!
  | ["set" ] => do IO.setCache $ ← Hashing.getHashes
  | ["clr" ] => do
    let hashMap ← Hashing.getHashes
    let except := hashMap.fold (fun acc _ hash => acc.insert s!"{IO.CACHEDIR}/{hash}.zip") default
    IO.clrCache except
    return 0
  | ["clr!"] => do IO.clrCache; return 0
  | _ => do
    IO.println help
    return 0
