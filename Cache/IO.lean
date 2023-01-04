/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean.Data.HashMap
import Lean.Data.RBMap
import Lean.Data.RBTree

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

open System (FilePath)

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

def LAKEPACKAGESDIR : FilePath :=
  ⟨"lake-packages"⟩

abbrev PackageDirs := Lean.RBMap String FilePath compare

/-- Whether this is running on Mathlib repo or not -/
def isMathlibRoot : IO Bool :=
  FilePath.mk "Mathlib" |>.pathExists

def mathlibDepPath : FilePath :=
  LAKEPACKAGESDIR / "Mathlib"

def getPackageDirs : IO PackageDirs := return .ofList [
  ("Mathlib", if ← isMathlibRoot then "." else mathlibDepPath),
  ("Aesop", LAKEPACKAGESDIR / "aesop"),
  ("Std", LAKEPACKAGESDIR / "std"),
  ("Qq", LAKEPACKAGESDIR / "Qq")
]

initialize pkgDirs : PackageDirs ← getPackageDirs

def getPackageDir (path : FilePath) : IO FilePath :=
  match path.withExtension "" |>.components.head? with
  | none => throw $ IO.userError "Can't find package directory for empty path"
  | some pkg => match pkgDirs.find? pkg with
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
    (← fp.readDir).foldlM (fun acc dir => getFilesWithExtension dir.path extension acc) acc
  else return if fp.extension == some extension then acc.push fp else acc

abbrev HashMap := Lean.HashMap FilePath UInt64

namespace HashMap

def filter (hashMap : HashMap) (set : Lean.RBTree String compare) (keep : Bool) : HashMap :=
  hashMap.fold (init := default) fun acc path hash =>
    let contains := set.contains hash.asTarGz
    let add := if keep then contains else !contains
    if add then acc.insert path hash else acc

def hashes (hashMap : HashMap) : Lean.RBTree UInt64 compare :=
  hashMap.fold (init := default) fun acc _ hash => acc.insert hash

end HashMap

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
      discard $ runCmd "tar" $ #["-I", "gzip -9", "-cf", zipPath.toString] ++
        (← mkBuildPaths path)
    acc := acc.push zip
  return acc

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO $ Lean.RBTree String compare := do
  let paths ← getFilesWithExtension CACHEDIR "gz"
  return .ofList (paths.data.map (·.withoutParent CACHEDIR |>.toString))

/-- Decompresses build files into their respective folders -/
def setCache (hashMap : HashMap) : IO Unit := do
  IO.println "Decompressing cache"
  hashMap.filter (← getLocalCacheSet) true |>.forM fun path hash => do
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
def clearCache (keep : Lean.RBTree FilePath compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "gz" do
    if ! keep.contains path then IO.FS.removeFile path

end Cache.IO
