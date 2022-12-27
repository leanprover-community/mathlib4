import Cache.Hashing

def ByteArray.startsWith (a b : ByteArray) : Bool := Id.run do
  let size := b.size
  let a := a.copySlice 0 .empty 0 size
  if size != a.size then return false
  for i in [0 : size] do
    if a.get! i != b.get! i then return false
  return true

namespace Cache.Requests

/-- Azure blob URL -/
def URL : String :=
  "https://lakecache.blob.core.windows.net/mathlib4"

open System

/-- Retrieves the azure token from the file system -/
def getToken : IO String := do
  let some token ← IO.getEnv "MATHLIB_CACHE_SAS"
    | throw (IO.userError "environment variable MATHLIB_CACHE_SAS must be set to upload caches")
  return token

/-- Gets the set of file names hosted on the the server -/
def getHostedCacheSet : IO $ Std.RBSet String compare := do
  IO.println "Downloading list of hosted files"
  let ret ← IO.runCmd "curl" #["-X", "GET", s!"{URL}?comp=list&restype=container"]
  match ret.splitOn "<Name>" with
  | [] | [_] => return default
  | _ :: parts =>
    let names : List String ← parts.mapM fun part =>
      match part.splitOn "</Name>" with
      | [] | [_] => throw $ IO.userError "Invalid format for curl return"
      | name :: _ => pure name
    return .ofList names _

/-- Given a file name like `"1234.tar.gz"`, makes the URL to that file on the server -/
def mkFileURL (fileName : String) (token : Bool) : IO String :=
  return if token then s!"{URL}/{fileName}?{← getToken}" else s!"{URL}/{fileName}"

section Put

/-- Formats part of the `curl` command that corresponds to the listing of files to be uploaded -/
def mkPutPairs (fileNames : Array String) : IO $ Array String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure $ acc.append #["-T", s!"{IO.CACHEDIR}/{fileName}", ← mkFileURL fileName true]

/-- Calls `curl` to send a set of cached files to the server -/
def putFiles (fileNames : Array String) (overwrite : Bool) : IO UInt32 := do
  let size := fileNames.size
  if size > 0 then
    IO.println s!"Attempting to upload {size} file(s)"
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "--parallel"]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *", "--parallel"]
    discard $ IO.runCmd "curl" $ params ++ (← mkPutPairs fileNames)
  else IO.println "No file to upload"
  return 0

end Put

section Get

/-- Formats part of the `curl` command that corresponds to the listing of files to be downloaded -/
def mkGetPairs (fileNames : Array $ String × FilePath) : IO $ Array String :=
  fileNames.foldlM (init := default) fun acc (fileName, path) => do
    pure $ acc ++ #[← mkFileURL fileName false, "-o", path.toString]

def invalidFileStart : ByteArray :=
  ⟨#[239, 187, 191, 60, 63, 120, 109, 108, 32, 118, 101, 114, 115, 105, 111, 110, 61]⟩

/--
Calls `curl` to download files from the server.

It first downloads the files to a temporary folder then extracts valit `tar.gz` files to the cache
folder. The temporary folder is then deleted.
-/
def getFiles (hashMap : IO.HashMap) : IO UInt32 := do
  IO.mkDir IO.TMPDIR
  let size := hashMap.size
  if size > 0 then
    let pairs := hashMap.fold (init := #[]) fun acc _ hash =>
      let fileName := hash.asTarGz
      acc.push (fileName, IO.TMPDIR / fileName)
    IO.println s!"Attempting to download {size} file(s)"
    discard $ IO.runCmd "curl" $ #["-X", "GET", "--parallel"] ++ (← mkGetPairs pairs)
    for (fileName, path) in pairs do
      let bytes ← IO.FS.readBinFile path
      if !bytes.startsWith invalidFileStart then
        IO.FS.writeBinFile (IO.CACHEDIR / fileName) bytes
    IO.FS.removeDirAll IO.TMPDIR
    IO.setCache hashMap
  else IO.println "No file to download"; return 0

/-- Tries to download missing (linked) files from the server -/
def getCache : IO UInt32 := do
  let localCacheSet ← IO.getLocalCacheSet
  let hashMap ← Hashing.getHashes
  getFiles $ hashMap.filter fun _ hash => !localCacheSet.contains hash.asTarGz

/-- Tries to download all (linked) files from the server -/
def getCache! : IO UInt32 := do
  getFiles $ ← Hashing.getHashes

end Get

/-- WIP garbage collection. Currently deletes the entire cache. Still useful for development -/
def gbgCache : IO UInt32 := do
  let hostedCacheSet ← getHostedCacheSet
  let arr ← hostedCacheSet.foldlM (init := #[]) fun acc fileName => do
    pure $ acc.push (← mkFileURL fileName true)
  discard $ IO.runCmd "curl" $ #["-X", "DELETE", "--parallel"] ++ arr
  return 0

end Cache.Requests
