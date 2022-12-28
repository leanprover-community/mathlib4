import Lean.Elab.ParseImportsFast
import Std.Data.HashMap
import Std.Data.RBMap

/-- Removes a parent path from the beginning of a path -/
def System.FilePath.withoutParent (path parent : FilePath) : FilePath :=
  let rec aux : List String → List String → List String
    | z@(x :: xs), y :: ys => if x == y then aux xs ys else z
    | [], _ => []
    | x, [] => x
  mkFilePath $ aux path.components parent.components

namespace Cache.IO

open System

/-- Target directory for build files -/
def LIBDIR : FilePath :=
  "build" / "lib"

/-- Target directory for IR files -/
def IRDIR : FilePath :=
  "build" / "ir"

/-- Target directory for caching -/
def CACHEDIR : FilePath :=
  ⟨".cache"⟩

/-- Target directory for caching -/
def TMPDIR : FilePath :=
  ⟨".cache/tmp"⟩

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 then throw $ IO.userError out.stderr
  else return out.stdout

/-- Recursively gets all files from a directory with a certain extension -/
partial def getFilesWithExtension
  (fp : FilePath) (extension : String) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    let mut acc := acc
    for dirEntry in ← fp.readDir do
      acc ← getFilesWithExtension dirEntry.path extension acc
    return acc
  else if fp.extension == some extension then return acc.push fp else return acc

/-- Given a path to a Lean file, concatenates the paths to its build files -/
def mkBuildPaths (leanPath : FilePath) : Array String :=
  #[
    LIBDIR / leanPath.withExtension "olean" |>.toString,
    LIBDIR / leanPath.withExtension "ilean" |>.toString,
    LIBDIR / leanPath.withExtension "trace" |>.toString,
    IRDIR / leanPath.withExtension "c" |>.toString,
    IRDIR / leanPath.withExtension "c.trace" |>.toString
  ]

abbrev HashMap := Std.HashMap FilePath UInt64

def _root_.UInt64.asTarGz (n : UInt64) : String :=
  s!"{n}.tar.gz"

def mkDir (path : FilePath) : IO Unit := do
  if !(← path.pathExists) then IO.FS.createDirAll path

/-- Compresses build files into the local cache -/
def mkCache (hashMap : HashMap) : IO $ Array String := do
  mkDir CACHEDIR
  IO.println "Compressing cache"
  let mut acc := default
  for (path, hash) in hashMap.toList do
    let hashZip := hash.asTarGz
    let hashZipPath := CACHEDIR / hashZip
    if !(← hashZipPath.pathExists) then
      discard $ runCmd "tar" $ #["-I", "gzip -9", "-cf", hashZipPath.toString] ++ mkBuildPaths path
    acc := acc.push hashZip
  return acc

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO $ Std.RBSet String compare := do
  let paths ← getFilesWithExtension CACHEDIR "gz"
  return .ofArray (paths.map (·.withoutParent CACHEDIR |>.toString)) _

/-- Decompresses build files into their respective folders -/
def setCache (hashMap : HashMap) : IO Unit := do
  IO.println "Decompressing cache"
  let localCacheSet ← getLocalCacheSet
  (hashMap.filter fun _ hash => localCacheSet.contains hash.asTarGz).forM fun path hash =>
    match path.parent with
    | none => throw $ IO.userError s!"Can't infer target build folder for {path}"
    | some path => do
      mkDir $ LIBDIR / path
      mkDir $ IRDIR / path
      discard $ runCmd "tar" #["-xzf", s!"{CACHEDIR / hash.asTarGz}"]

instance : Ord FilePath where
  compare x y := compare x.toString y.toString

/-- Retrieves the azure token from the file system -/
def getToken : IO String := do
  let some token ← IO.getEnv "MATHLIB_CACHE_SAS"
    | throw (IO.userError "environment variable MATHLIB_CACHE_SAS must be set to upload caches")
  return token

/-- Removes all cache files except for what's in the `keep` set -/
def clearCache (keep : Std.RBSet FilePath compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "gz" do
    if ! keep.contains path then IO.FS.removeFile path

end Cache.IO
