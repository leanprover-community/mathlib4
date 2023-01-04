/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

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

open System (FilePath)

/--
Given a file name like `"1234.tar.gz"`, makes the URL to that file on the server.

The `f/` prefix means that it's a common file for caching.
-/
def mkFileURL (fileName : String) (token : Option String) : IO String :=
  return match token with
  | some token => s!"{URL}/f/{fileName}?{token}"
  | none => s!"{URL}/f/{fileName}"

section Get

/-- Formats part of the `curl` command that corresponds to the listing of files to be downloaded -/
def mkGetPairs (fileNames : Array $ String × FilePath) : IO $ Array String :=
  fileNames.foldlM (init := default) fun acc (fileName, path) => do
    pure $ acc ++ #[← mkFileURL fileName none, "-o", path.toString]

/-- Bytes that correspond to the beginning of invalid downloaded files, introducing a XML -/
def invalidFileStart : ByteArray :=
  ⟨#[239, 187, 191, 60, 63, 120, 109, 108, 32, 118, 101, 114, 115, 105, 111, 110, 61]⟩

/--
Calls `curl` to download files from the server.

It first downloads the files to a temporary folder then extracts valid `tar.gz` files to the cache
folder. The temporary folder is then deleted.
-/
def getFiles (hashMap : IO.HashMap) : IO Unit := do
  let size := hashMap.size
  if size > 0 then
    let pairs := hashMap.fold (init := #[]) fun acc _ hash =>
      let fileName := hash.asTarGz
      acc.push (fileName, IO.TMPDIR / fileName)
    IO.println s!"Attempting to download {size} file(s)"
    IO.mkDir IO.TMPDIR
    discard $ IO.runCmd "curl" $ #["-X", "GET", "--parallel"] ++ (← mkGetPairs pairs)
    for (fileName, path) in pairs do
      let bytes ← IO.FS.readBinFile path
      if !bytes.startsWith invalidFileStart then
        IO.FS.writeBinFile (IO.CACHEDIR / fileName) bytes
    IO.FS.removeDirAll IO.TMPDIR
    IO.setCache hashMap
  else IO.println "No file to download"

end Get

section Put

/-- Formats part of the `curl` command that corresponds to the listing of files to be uploaded -/
def mkPutPairs (fileNames : Array String) (token : String) : IO $ Array String :=
  fileNames.foldlM (init := default) fun acc fileName => do
    pure $ acc.append #["-T", s!"{IO.CACHEDIR / fileName}", ← mkFileURL fileName (some token)]

/-- Calls `curl` to send a set of cached files to the server -/
def putFiles (fileNames : Array String) (overwrite : Bool) (token : String) : IO Unit := do
  let size := fileNames.size
  if size > 0 then
    IO.println s!"Attempting to upload {size} file(s)"
    let params := if overwrite
      then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "--parallel"]
      else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *", "--parallel"]
    discard $ IO.runCmd "curl" $ params ++ (← mkPutPairs fileNames token)
  else IO.println "No file to upload"

end Put

section Commit

def isStatusClean : IO Bool :=
  return (← IO.runCmd "git" #["status", "--porcelain"]).isEmpty

def getCommitHash : IO String := do
  let ret := (← IO.runCmd "git" #["log", "-1"]).replace "\n" " "
  match ret.splitOn " " with
  | "commit" :: hash :: _ => return hash
  | _ => throw $ IO.userError "Invalid format for the return of `git log -1`"

/--
Sends a commit file to the server, containing the hashes of the respective commited files.

The file name is the current Git hash and the `c/` prefix means that it's a commit file.
-/
def commit (hashMap : IO.HashMap) (overwrite : Bool) (token : String) : IO Unit := do
  let hash ← getCommitHash
  let path := IO.TMPDIR / hash
  IO.mkDir IO.TMPDIR
  IO.FS.writeFile path $ ("\n".intercalate $ hashMap.hashes.toList.map toString) ++ "\n"
  let params := if overwrite
    then #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob"]
    else #["-X", "PUT", "-H", "x-ms-blob-type: BlockBlob", "-H", "If-None-Match: *"]
  discard $ IO.runCmd "curl" $ params ++ #["-T", path.toString, s!"{URL}/c/{hash}?{token}"]
  IO.FS.removeDirAll IO.TMPDIR

end Commit

section Collect

inductive QueryType
  | files | commits | all

def QueryType.prefix : QueryType → String
  | files   => "&prefix=f/"
  | commits => "&prefix=c/"
  | all     => default

def formatError : IO α :=
  throw $ IO.userError "Invalid format for curl return"

def QueryType.desc : QueryType → String
  | files   => "hosted files"
  | commits => "hosted commits"
  | all     => "everything"

/--
Retrieves metadata about hosted files: their names and the timestamps of last modification.

Example: `["path/to/file.extension", "Sat, 24 Dec 2022 17:33:01 GMT"]`
-/
def getFilesInfo (q : QueryType) : IO $ List (String × String) := do
  IO.println s!"Downloading info list of {q.desc}"
  let ret ← IO.runCmd "curl" #["-X", "GET", s!"{URL}?comp=list&restype=container{q.prefix}"]
  match ret.splitOn "<Name>" with
  | [] => formatError
  | [_] => return default
  | _ :: parts =>
    parts.mapM fun part => match part.splitOn "</Name>" with
      | [name, rest] => match rest.splitOn "<Last-Modified>" with
        | [_, rest] => match rest.splitOn "</Last-Modified>" with
          | [date, _] => pure (name, date)
          | _ => formatError
        | _ => formatError
      | _ => formatError

/-- WIP garbage collection. Currently deletes the entire cache. Still useful for development -/
def collectCache (token : String) : IO Unit := do
  let hostedCacheSet ← getFilesInfo .all
  let arr ← hostedCacheSet.foldlM (init := #[]) fun acc (fileName, _) => do
    pure $ acc.push (← mkFileURL fileName (some token))
  discard $ IO.runCmd "curl" $ #["-X", "DELETE", "--parallel"] ++ arr

end Collect

end Cache.Requests
