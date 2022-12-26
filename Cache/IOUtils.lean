import Lean.Elab.ParseImportsFast
import Std.Data.HashMap
import Std.Data.RBMap

namespace System.FilePath

def withoutParent (path : FilePath) (parent : FilePath) : FilePath :=
  let rec aux : List String → List String → List String
    | z@(x :: xs), y :: ys => if x == y then aux xs ys else z
    | [], _ => []
    | x, [] => x
  ⟨"/".intercalate $ aux (path.toString.splitOn "/") (parent.toString.splitOn "/")⟩

def getFileImports (content : String) : Array FilePath :=
  let s := Lean.ParseImports.main content (Lean.ParseImports.whitespace content {})
  let imps := s.imports.map (·.module.toString) |>.filter (·.startsWith "Mathlib.")
  imps.map fun imp => (FilePath.mk $ imp.replace "." "/").withExtension "lean"

end System.FilePath

namespace Cache.IO

open System

def LIBDIR : FilePath :=
  "build" / "lib"

def CACHEDIR : FilePath :=
  ⟨"cache"⟩

partial def getFilesWithExtension
  (fp : FilePath) (extension : String) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    let mut acc := acc
    for dirEntry in ← fp.readDir do
      for innerFp in ← getFilesWithExtension dirEntry.path extension do
        acc := acc.push innerFp
    return acc
  else if fp.extension == some extension then return acc.push fp else return acc

def getBuiltFilesWithExtension (extension : String) : IO $ Array FilePath :=
  return (← getFilesWithExtension (LIBDIR / "Mathlib") extension).map (·.withoutParent LIBDIR)

def mkDir (path : FilePath) : IO Unit := do
  if !(← path.pathExists) then IO.FS.createDir path else pure ()

def copyCache (hashes : Std.HashMap FilePath UInt64) : IO $ Std.RBSet String compare := do
  mkDir CACHEDIR
  let mut res := default
  for extension in ["olean", "ilean", "trace"] do
    for path in ← getBuiltFilesWithExtension extension do
    match hashes.find? $ path.withExtension "lean" with
    | none => pure ()
    | some hash =>
      let targetFileStem := s!"{hash}.{extension}"
      let targetPath := CACHEDIR / targetFileStem
      IO.FS.writeBinFile targetPath $ ← IO.FS.readBinFile (LIBDIR / path)
      res := res.insert targetFileStem
  return res

def setCache (hashes : Std.HashMap FilePath UInt64) : IO Unit :=
  hashes.forM fun filePath fileHash =>
    for extension in ["olean", "ilean", "trace"] do
      let builtFilePath := CACHEDIR / toString fileHash |>.withExtension extension
      if ← builtFilePath.pathExists then
        let targetPath := LIBDIR / filePath |>.withExtension extension
        match targetPath.parent with
        | some dir => mkDir dir; IO.FS.writeBinFile targetPath $ ← IO.FS.readBinFile builtFilePath
        | none => pure ()

def getLocalCacheSet : IO $ Std.RBSet String compare :=
  ["olean", "ilean", "trace"].foldlM (init := default) fun acc extension => do
    (← getFilesWithExtension CACHEDIR extension).foldlM (init := acc) fun acc path =>
      pure $ acc.insert (path.withoutParent CACHEDIR).toString

def clearCache (exceptHashes : Std.RBSet String compare) : IO Unit :=
  for extension in ["olean", "ilean", "trace"] do
    for path in ← getFilesWithExtension CACHEDIR extension do
      match (path.withoutParent CACHEDIR).fileStem with
      | none => continue
      | some hash =>
        if exceptHashes.contains hash then continue
        IO.FS.removeFile path

end Cache.IO
