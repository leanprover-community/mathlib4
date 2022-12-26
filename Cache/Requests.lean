import Cache.Hashing

def List.pop : (l : List α) → l ≠ [] → α × Array α
  | a :: as, _ => (a, ⟨as⟩)

namespace Cache.Requests

def URL : String :=
  "https://lakecache.blob.core.windows.net/mathlib4"

open System

def getToken : IO String :=
  return (← IO.FS.readFile ⟨"azure.token"⟩).trim

def runCmd (cmd : String) : IO String := do
  let cmd := cmd.splitOn " "
  if h : cmd ≠ [] then
    let (cmd, args) := match h' : cmd with
      | cmd :: args => (cmd, ⟨args⟩)
      | []          => absurd h' (h' ▸ h)
    let out ← IO.Process.output {
      cmd  := cmd
      args := args
    }
    if out.exitCode != 0
      then throw $ IO.userError out.stderr
      else return out.stdout
  else return ""

def spawnCmd (cmd : String) : IO UInt32 := do
  let cmd := cmd.splitOn " "
  if h : cmd ≠ [] then
    let (cmd, args) := cmd.pop h
    let child ← IO.Process.spawn {
      cmd := cmd
      args := args
    }
    child.wait
  else return 0

def getHostedCacheSet : IO $ Std.RBSet String compare := do
  IO.println "Downloading list hosted files"
  let ret ← runCmd s!"curl -X GET {URL}?comp=list&restype=container&{← getToken}"
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
    spawnCmd $ s!"curl -X PUT -H \"x-ms-blob-type: BlockBlob\" --parallel --progress-bar"
      ++ s!"{← mkPutPairs fileNames} | cat"
  else
    IO.println "No file to upload"
    return 0

def putCache : IO UInt32 := do
  let hostedCacheSet ← getHostedCacheSet
  let localCacheSet ← IO.copyCache $ ← Hashing.getHashes
  putFiles $ localCacheSet.filter (! hostedCacheSet.contains ·)

def putCache! : IO UInt32 := do
  putFiles $ ← IO.copyCache $ ← Hashing.getHashes

end Put

section Get

def mkGetPairs (fileNames : Std.RBSet String compare) : IO String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure s!"{acc} {← mkFileURL fileName} -o {IO.CACHEDIR}/{fileName}"

def getFiles (fileNames : Std.RBSet String compare) (hashMap : Std.HashMap FilePath UInt64) : IO UInt32 := do
  discard $ IO.copyCache hashMap
  let size := fileNames.size
  if size > 0 then
    IO.println s!"Downloading {size} file(s)"
    let ret ← spawnCmd s!"curl -X GET --parallel --progress-bar{← mkGetPairs fileNames}"
    if ret == 0 then IO.setCache hashMap else return ret
  else
    IO.println "No file to download"
    return 0

def getAvailableFileNames (hashMap : Std.HashMap FilePath UInt64) : IO $ Std.RBSet String compare := do
  let hostedCacheSet ← getHostedCacheSet
  return IO.CACHEEXTENSIONS.foldl (init := default) fun acc extension =>
    hashMap.fold (init := acc) fun acc _ hash =>
      let fileName := s!"{hash}.{extension}"
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
