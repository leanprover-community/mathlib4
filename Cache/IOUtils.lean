import Lean.Elab.ParseImportsFast

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

def LIBDIR : FilePath :=
  "build" / "lib"

def CACHEDIR : FilePath := "cache"

def getExistingBuiltFilesWithExtension (extension : String) : IO $ Array FilePath :=
  return (← getFilesWithExtension (LIBDIR / "Mathlib") extension).map (·.withoutParent LIBDIR)

def mkCacheDir : IO Unit := do
  if !(← CACHEDIR.pathExists) then IO.FS.createDir CACHEDIR else pure ()

def copyCache (hashes : Lean.HashMap FilePath UInt64) : IO $ Array FilePath := do
  let mut res := #[]
  for extension in ["olean", "ilean", "trace"] do
    for path in ← getExistingBuiltFilesWithExtension extension do
    match hashes.find? $ path.withExtension "lean" with
    | none => pure ()
    | some hash =>
      let targetPath := CACHEDIR / (FilePath.mk (toString hash)).withExtension extension
      IO.FS.writeBinFile targetPath $ ← IO.FS.readBinFile (LIBDIR / path)
      res := res.push targetPath
  return res

def setCache (hashes : Lean.HashMap FilePath UInt64) : IO Unit :=
  hashes.forM fun filePath fileHash => do
    for extension in ["olean", "ilean", "trace"] do
      let builtFilePath := CACHEDIR / toString fileHash |>.withExtension extension
      if ← builtFilePath.pathExists then
        let targetBuiltPath := LIBDIR / filePath |>.withExtension extension
        IO.FS.writeBinFile targetBuiltPath $ ← IO.FS.readBinFile builtFilePath

end Cache.IO
