import Lean.Elab.ParseImportsFast
import Std.Data.HashMap
import Std.Data.RBMap

def List.pop : (l : List α) → l ≠ [] → α × Array α
  | a :: as, _ => (a, ⟨as⟩)

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

def mkBuildPaths (leanPath : FilePath) : String :=
  " ".intercalate [
    LIBDIR / leanPath.withExtension "olean" |>.toString,
    LIBDIR / leanPath.withExtension "ilean" |>.toString,
    LIBDIR / leanPath.withExtension "trace" |>.toString
  ]

abbrev HashMap := Std.HashMap FilePath UInt64

def zipCache (hashMap : HashMap) : IO $ Std.RBSet String compare := do
  mkDir CACHEDIR
  IO.println "Compressing cache"
  hashMap.foldM (init := default) fun acc path hash => do
    let cacheHash := CACHEDIR / toString hash
    let cacheHashZip := cacheHash.withExtension "zip"
    let hashZip := s!"{hash}.zip"
    if !(← cacheHashZip.pathExists) then
      let ret ← spawnCmd s!"zip -q -9 {CACHEDIR / toString hash} {mkBuildPaths path}"
      if ret != 0 then throw $ IO.userError s!"Error when compressing cache for {path}"
      else pure $ acc.insert hashZip
    else pure $ acc.insert hashZip

def setCache (hashMap : HashMap) : IO UInt32 := do
  IO.println "Decompressing cache"
  hashMap.forM fun path hash =>
    match path.parent with
    | none => throw $ IO.userError s!"Can't infer target build folder for {path}"
    | some path => do
      let ret ← spawnCmd s!"unzip -qq -o {CACHEDIR}/{hash}.zip -d {LIBDIR / path}"
      if ret != 0 then throw $ IO.userError s!"Error when decompressing cache for {path}"
  return 0

def getLocalCacheSet : IO $ Std.RBSet String compare := do
  let paths ← getFilesWithExtension CACHEDIR "zip"
  return .ofArray (paths.map (·.withoutParent CACHEDIR |>.toString)) _

def clrCache (except : Std.RBSet String compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "zip" do
    if ! except.contains path.toString then IO.FS.removeFile path

end Cache.IO
