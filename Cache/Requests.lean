import Cache.Hashing

namespace Cache.Requests

def URL : String :=
  "https://lakecache.blob.core.windows.net/mathlib4"

open System

def getToken : IO String :=
  return (← IO.FS.readFile ⟨"azure.token"⟩).trim

def getHostedCacheSet : IO $ Std.RBSet String compare := do
  IO.println "Downloading list hosted files"
  let ret ← IO.runCmd s!"curl -X GET {URL}?comp=list&restype=container&{← getToken}"
  match ret.splitOn "<Name>" with
  | [] | [_] => default
  | _ :: parts =>
    let names : List String ← parts.mapM fun part =>
      match part.splitOn "</Name>" with
      | [] | [_] => throw $ IO.userError "Invalid format for curl return"
      | name :: _ => pure name
    return .ofList names _

def mkFileURL (fileName : String) : IO String :=
  return s!"{URL}/{fileName}?{← getToken}"

section Put

def mkPutPairs (fileNames : Std.RBSet String compare) : IO String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure s!"{acc} -T {IO.CACHEDIR}/{fileName} \"{← mkFileURL fileName}\""

def putFiles (fileNames : Std.RBSet String compare) : IO UInt32 := do
  let size := fileNames.size
  if size > 0 then
    IO.println s!"Uploading {size} file(s)"
    IO.spawnCmd $ s!"curl -X PUT -H \"x-ms-blob-type: BlockBlob\" --parallel --progress-bar"
      ++ s!"{← mkPutPairs fileNames} | cat"
  else
    IO.println "No file to upload"
    return 0

def putCache : IO UInt32 := do
  let hostedCacheSet ← getHostedCacheSet
  let hashMap := (← Hashing.getHashes).filter fun _ hash =>
    !(hostedCacheSet.contains s!"{hash}.zip")
  let localCacheSet ← IO.zipCache hashMap
  putFiles localCacheSet

def putCache! : IO UInt32 := do
  putFiles $ ← IO.zipCache $ ← Hashing.getHashes

end Put

section Get

def mkGetPairs (fileNames : Std.RBSet String compare) : IO String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure s!"{acc} {← mkFileURL fileName} -o {IO.CACHEDIR}/{fileName}"

def getFiles (fileNames : Std.RBSet String compare) (hashMap : Std.HashMap FilePath UInt64) : IO UInt32 := do
  let size := fileNames.size
  if size > 0 then
    IO.println s!"Downloading {size} file(s)"
    let ret ← IO.spawnCmd s!"curl -X GET --parallel --progress-bar{← mkGetPairs fileNames}"
    if ret == 0 then IO.setCache hashMap else return ret
  else
    IO.println "No file to download"
    return 0

def getAvailableFileNames (hashMap : IO.HashMap) : IO $ Std.RBSet String compare := do
  let hostedCacheSet ← getHostedCacheSet
  return hashMap.fold (init := default) fun acc _ hash =>
    let fileName := s!"{hash}.zip"
    if hostedCacheSet.contains fileName then acc.insert fileName else acc

def getCache : IO UInt32 := do
  let localCacheSet ← IO.getLocalCacheSet
  let hashMap ← Hashing.getHashes
  getFiles ((← getAvailableFileNames hashMap).filter (! localCacheSet.contains ·)) hashMap

def getCache! : IO UInt32 := do
  let hashMap ← Hashing.getHashes
  getFiles (← getAvailableFileNames hashMap) hashMap

end Get

end Cache.Requests
