import Cache.Hashing

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
def mkPutPairs (fileNames : Std.RBSet String compare) : IO $ Array String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure $ acc.append #["-T", s!"{IO.CACHEDIR}/{fileName}", ← mkFileURL fileName true]

/-- Calls `curl` to send a set of cache files to the server -/
def putFiles (fileNames : Std.RBSet String compare) (overwrite : Bool) : IO UInt32 := do
  let size := fileNames.size
  if size > 0 then
    IO.println s!"Uploading {size} file(s)"
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "--parallel"]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *", "--parallel"]
    discard $ IO.runCmd "curl" $ params ++ (← mkPutPairs fileNames)
  else
    IO.println "No file to upload"
  return 0

/-- Sends missing (linked) cache files to the server -/
def putCache : IO UInt32 := do
  putFiles (← IO.zipCache $ ← Hashing.getHashes) false

/-- Sends all (linked) cache files to the server -/
def putCache! : IO UInt32 := do
  putFiles (← IO.zipCache $ ← Hashing.getHashes) true

end Put

section Get

/-- Formats part of the `curl` command that corresponds to the listing of files to be downloaded -/
def mkGetPairs (fileNames : Std.RBSet String compare) : IO $ Array String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure $ acc ++ #[← mkFileURL fileName false, "-o", s!"{IO.CACHEDIR / fileName}"]

/-- Calls `curl` to download files from the server -/
def getFiles (hashMap : IO.HashMap) : IO UInt32 := do
  IO.mkDir IO.TMPDIR
  let size := hashMap.size
  if size > 0 then
    -- download into `IO.TMPDIR`
    -- move real tar.gz files into `IO.CACHEDIR`
    -- delete `IO.TMPDIR`
    -- get rid of `spawnCmd`
    sorry
  else IO.println "No file to download"; return 0

-- /-- Calls `curl` to download files from the server -/
-- def getFiles (fileNames : Std.RBSet String compare) (hashMap : IO.HashMap) : IO UInt32 := do
--   IO.mkDir IO.CACHEDIR
--   let size := fileNames.size
--   if size > 0 then
--     IO.println s!"Downloading {size} file(s)"
--     let ret ← IO.spawnCmd "curl" $ #["-X", "GET", "--parallel", "--progress-bar"]
--       ++ (← mkGetPairs fileNames)
--     if ret == 0 then IO.setCache hashMap else return ret
--   else
--     IO.println "No file to download"
--     return 0

/-- Gets the list of needed files that are available on the server -/
def getAvailableFileNames (hashMap : IO.HashMap) : IO $ Std.RBSet String compare := do
  let hostedCacheSet ← getHostedCacheSet
  return hashMap.fold (init := default) fun acc _ hash =>
    let fileName := s!"{hash}.tar.gz"
    if hostedCacheSet.contains fileName then acc.insert fileName else acc

/-- Downloads missing (linked) files from the server -/
def getCache : IO UInt32 := do
  let localCacheSet ← IO.getLocalCacheSet
  let hashMap ← Hashing.getHashes
  getFiles $ hashMap.filter fun _ hash => !(localCacheSet.contains s!"{hash}.tar.gz")

/-- Downloads all (linked) files from the server -/
def getCache! : IO UInt32 := do
  getFiles $ ← Hashing.getHashes

end Get

/-- WIP garbage collection. Currently deletes the entire cache. Still useful for development -/
def gbgCache : IO UInt32 := do
  let hostedCacheSet ← getHostedCacheSet
  let arr ← hostedCacheSet.foldlM (init := #[]) fun acc fileName => do
    pure $ acc.push (← mkFileURL fileName true)
  IO.spawnCmd "curl" $ #["-X", "DELETE", "--parallel"] ++ arr

end Cache.Requests
