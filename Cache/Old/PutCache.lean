import Caching.Utils

open System

def curlInit : String :=
  s!"curl -X PUT -H \"Authorization: Bearer {TOKEN}\" \"Content-Type: multipart/form-data\" {URL}"

def getExistingBuiltFilesWithExtension (extension : String) : IO $ Array FilePath := do
  return (← getFilePaths (LIBDIR / "Mathlib") extension).map
    (·.toString.splitOn s!"{LIBDIR}/" |>.get! 1)

def makeCache (hashMap : Lean.HashMap FilePath UInt64) : IO $ Array FilePath := do
  let cachePath : FilePath := ⟨"cache"⟩
  if !(← cachePath.pathExists) then IO.FS.createDir cachePath
  let mut res := #[]
  for kind in builtFileKinds do
    let kindExtension := kind.extension
    for path in ← getExistingBuiltFilesWithExtension kindExtension do
    match hashMap.find? $ path.withExtension "lean" with
    | none => pure ()
    | some hash =>
      let path' := (cachePath / (FilePath.mk (ToString.toString hash)).withExtension kindExtension)
      res := res.push path'
      IO.FS.writeBinFile path' $ ← IO.FS.readBinFile (LIBDIR / path)
  return res

def main : IO Unit := do
  -- TODO : `lake build`
  let hashes ← getHashes
  let caches ← makeCache hashes
  -- let curlCMD := hashes.fold (init := curlInit) fun acc filePath fileHash =>
  --   s!"{acc} {curlPieceForPair filePath fileHash}"
  let curlCMD := (caches.toList.take 2).foldl (init := curlInit) fun acc filePath =>
    s!"{acc} -F filename=@{filePath}"
  let curlCMD := s!"{curlCMD}"
  IO.println curlCMD
