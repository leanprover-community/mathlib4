import Lean.Elab.ParseImportsFast
import Std.Data.HashMap
import Std.Data.RBMap

def List.pop : (l : List α) → l ≠ [] → α × List α
  | a :: as, _ => (a, as)

/-- Removes a parent path from the beginning of a path -/
def System.FilePath.withoutParent (path : FilePath) (parent : FilePath) : FilePath :=
  let rec aux : List String → List String → List String
    | z@(x :: xs), y :: ys => if x == y then aux xs ys else z
    | [], _ => []
    | x, [] => x
  ⟨"/".intercalate $ aux (path.toString.splitOn "/") (parent.toString.splitOn "/")⟩

namespace Cache.IO

open System

/-- Target directory for build files -/
def LIBDIR : FilePath :=
  "build" / "lib"

/-- Target directory for caching -/
def CACHEDIR : FilePath :=
  ⟨"cache"⟩

/--
Runs a terminal command and retrieves its output. `↔` must be used as a placeholder for whitespaces
-/
def runCmd (cmd : String) : IO String := do
  let cmd := cmd.splitOn " " |>.map (·.replace "↔" " ")
  if h : cmd ≠ [] then
    let (cmd, args) := cmd.pop h
    let out ← IO.Process.output {
      cmd  := cmd
      args := ⟨args⟩
    }
    if out.exitCode != 0
      then throw $ IO.userError out.stderr
      else return out.stdout
  else return ""

/-- Spawns a terminal command. `↔` must be used as a placeholder for whitespaces -/
def spawnCmd (cmd : String) : IO UInt32 := do
  let cmd := cmd.splitOn " " |>.map (·.replace "↔" " ")
  if h : cmd ≠ [] then
    let (cmd, args) := cmd.pop h
    let child ← IO.Process.spawn {
      cmd  := cmd
      args := ⟨args⟩
    }
    child.wait
  else return 0

/-- Recursively gets all files from a directory with a certain extension -/
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

/-- Given a path to a Lean file, concatenates the paths to its build files -/
def mkBuildPaths (leanPath : FilePath) : String :=
  " ".intercalate [
    LIBDIR / leanPath.withExtension "olean" |>.toString,
    LIBDIR / leanPath.withExtension "ilean" |>.toString,
    LIBDIR / leanPath.withExtension "trace" |>.toString
  ]

abbrev HashMap := Std.HashMap FilePath UInt64

/-- Compresses build files into the local cache -/
def zipCache (hashMap : HashMap) : IO $ Std.RBSet String compare := do
  if !(← CACHEDIR.pathExists) then IO.FS.createDir CACHEDIR
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

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO $ Std.RBSet String compare := do
  let paths ← getFilesWithExtension CACHEDIR "zip"
  return .ofArray (paths.map (·.withoutParent CACHEDIR |>.toString)) _

/-- Decompresses build files into their respective folders -/
def setCache (hashMap : HashMap) : IO UInt32 := do
  IO.println "Decompressing cache"
  let localCacheSet ← getLocalCacheSet
  (hashMap.filter fun _ hash => localCacheSet.contains s!"{hash}.zip").forM fun path hash =>
    match path.parent with
    | none => throw $ IO.userError s!"Can't infer target build folder for {path}"
    | some path => do
      let ret ← spawnCmd s!"unzip -qq -o {CACHEDIR}/{hash}.zip -d {LIBDIR / path}"
      if ret != 0 then throw $ IO.userError s!"Error when decompressing cache for {path}"
  return 0

/-- Removes all cache files except for what's in the `keep` set -/
def clrCache (keep : Std.RBSet String compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "zip" do
    if ! keep.contains path.toString then IO.FS.removeFile path

end Cache.IO
