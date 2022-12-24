import Lean.Elab.ParseImportsFast

namespace System.FilePath

def withoutParent (path : FilePath) (parent : FilePath) : FilePath :=
  let parent := if parent.toString.endsWith "/" then parent else ⟨s!"{parent}/"⟩
  match path.toString.splitOn parent.toString with
  | [x] => ⟨x⟩
  | [_, x] => x
  | _ => panic! "invalid input"

def getFileImports (content : String) : Array FilePath :=
  let s := Lean.ParseImports.main content (Lean.ParseImports.whitespace content {})
  let imps := s.imports.map (·.module.toString) |>.filter (·.startsWith "Mathlib.")
  imps.map fun imp => (FilePath.mk $ imp.replace "." "/").withExtension "lean"

end System.FilePath

open System

namespace IO.FS

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
  return (← getFilesWithExtension (LIBDIR / "Mathlib") extension).map (.withoutParent · LIBDIR)

def mkCacheDir : IO Unit := do
  if !(← CACHEDIR.pathExists) then IO.FS.createDir CACHEDIR else pure ()

def copyCache (hashes : Lean.HashMap FilePath UInt64) : IO $ Array FilePath := do
  let mut res := #[]
  for extension in ["olean", "ilean", "trace"] do
    for path in ← getExistingBuiltFilesWithExtension extension do
    match hashes.find? $ path.withExtension "lean" with
    | none => pure ()
    | some hash =>
      let path' := (CACHEDIR / (FilePath.mk (toString hash)).withExtension extension)
      IO.FS.writeBinFile path' $ ← IO.FS.readBinFile (LIBDIR / path)
      res := res.push path'
  return res

def setCache (hashes : Lean.HashMap FilePath UInt64) : IO Unit := do
  let paths : Lean.HashMap UInt64 FilePath := hashes.fold (init := default) fun acc path hash =>
    acc.insert hash path
  -- TODO

end IO.FS
