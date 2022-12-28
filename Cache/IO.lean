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

def UInt64.asTarGz (n : UInt64) : String :=
  s!"{n}.tar.gz"

namespace Cache.IO

open System

def PACKAGESDIR : FilePath :=
  ⟨"lake-packages"⟩

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
  CACHEDIR / "tmp"

def packageMap : Std.RBMap String FilePath compare := .ofList [
  ("Mathlib", ⟨"."⟩),
  ("Aesop", PACKAGESDIR / "aesop"),
  ("Std", PACKAGESDIR / "std"),
  ("Qq", PACKAGESDIR / "Qq")
] _

def getPackageDir (path : FilePath) : IO FilePath :=
  match path.withExtension "" |>.components.head? with
  | none => throw $ IO.userError "Can't find package directory for empty path"
  | some pkg => match packageMap.find? pkg with
    | none => throw $ IO.userError s!"Unknown package directory for {pkg}"
    | some path => return path

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

abbrev HashMap := Std.HashMap FilePath UInt64

def mkDir (path : FilePath) : IO Unit := do
  if !(← path.pathExists) then IO.FS.createDirAll path

/-- Given a path to a Lean file, concatenates the paths to its build files -/
def mkBuildPaths (path : FilePath) : IO $ Array String := do
  let packageDir ← getPackageDir path
  return #[
    packageDir / LIBDIR / path.withExtension "olean"   |>.toString,
    packageDir / LIBDIR / path.withExtension "ilean"   |>.toString,
    packageDir / LIBDIR / path.withExtension "trace"   |>.toString,
    packageDir / IRDIR  / path.withExtension "c"       |>.toString,
    packageDir / IRDIR  / path.withExtension "c.trace" |>.toString]

/-- Compresses build files into the local cache -/
def mkCache (hashMap : HashMap) (overwrite : Bool) : IO $ Array String := do
  mkDir CACHEDIR
  IO.println "Compressing cache"
  let mut acc := default
  for (path, hash) in hashMap.toList do
    let zip := hash.asTarGz
    let zipPath := CACHEDIR / zip
    if overwrite || !(← zipPath.pathExists) then
      discard $ runCmd "tar" $ #["-I", "gzip -9", "-cf", zipPath.toString] ++ (← mkBuildPaths path)
    acc := acc.push zip
  return acc

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO $ Std.RBSet String compare := do
  let paths ← getFilesWithExtension CACHEDIR "gz"
  return .ofArray (paths.map (·.withoutParent CACHEDIR |>.toString)) _

/-- Decompresses build files into their respective folders -/
def setCache (hashMap : HashMap) : IO Unit := do
  IO.println "Decompressing cache"
  let localCacheSet ← getLocalCacheSet
  (hashMap.filter fun _ hash => localCacheSet.contains hash.asTarGz).forM fun path hash => do
    match path.parent with
    | none | some path => do
      let packageDir ← getPackageDir path
      mkDir $ packageDir / LIBDIR / path
      mkDir $ packageDir / IRDIR / path
    discard $ runCmd "tar" #["-xzf", s!"{CACHEDIR / hash.asTarGz}"]

instance : Ord FilePath where
  compare x y := compare x.toString y.toString

/-- Retrieves the azure token from the file system -/
def getToken : IO String := do
  let some token ← IO.getEnv "MATHLIB_CACHE_SAS"
    | throw $ IO.userError "environment variable MATHLIB_CACHE_SAS must be set to upload caches"
  return token

/-- Removes all cache files except for what's in the `keep` set -/
def clearCache (keep : Std.RBSet FilePath compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "gz" do
    if ! keep.contains path then IO.FS.removeFile path

end Cache.IO
