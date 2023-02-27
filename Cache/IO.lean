/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean.Data.HashMap
import Lean.Data.RBMap
import Lean.Data.RBTree
import Cache.Config

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
initialize CACHEDIR : FilePath ← do
  match ← IO.getEnv "XDG_CACHE_HOME" with
  | some path => return path / "lean4_cache"
  | none => match ← IO.getEnv "HOME" with
    | some path => return path / ".cache" / "lean4_cache"
    | none => pure ⟨".cache"⟩

/-- Target file path for `curl` configurations -/
def CURLCFG :=
  IO.CACHEDIR / "curl.cfg"

def getPackageDir (pkgDirs : PkgDirs) (path : FilePath) : IO FilePath :=
  match path.withExtension "" |>.components.head? with
  | none => throw $ IO.userError "Can't find package directory for empty path"
  | some pkg => match pkgDirs.find? pkg with
    | none => throw $ IO.userError s!"Unknown package directory for {pkg}"
    | some path => return path

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

def validateCurl : IO Bool := do
  match (← runCmd "curl" #["--version"]).splitOn " " with
  | "curl" :: v :: _ => match v.splitOn "." with
    | maj :: min :: _ =>
      let (maj, min) := (maj.toNat!, min.toNat!)
      if maj > 7 then return true
      if maj == 7 && min >= 69 then
        if min < 81 then
          IO.println s!"Warning: recommended `curl` version ≥7.81. Found {v}"
        return true
      else
        IO.println s!"`curl` version is required to be ≥7.69. Found {v}. Exiting..."
        return false
    | _ => throw $ IO.userError "Invalidly formatted version of `curl`"
  | _ => throw $ IO.userError "Invalidly formatted response from `curl --version`"

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
def mkBuildPaths (pkgDirs : PkgDirs) (path : FilePath) : IO $ Array FilePath := do
  let pkgDir ← getPackageDir pkgDirs path
  return #[
    pkgDir / LIBDIR / path.withExtension "olean",
    pkgDir / LIBDIR / path.withExtension "ilean",
    pkgDir / LIBDIR / path.withExtension "trace",
    pkgDir / IRDIR  / path.withExtension "c",
    pkgDir / IRDIR  / path.withExtension "c.trace"]

def allExist (paths : Array FilePath) : IO Bool := do
  for path in paths do
    if !(← path.pathExists) then return false
  pure true

/-- Compresses build files into the local cache and returns an array with the compressed files -/
def packCache (pkgDirs : PkgDirs) (hashMap : HashMap) (overwrite : Bool) : IO $ Array String := do
  mkDir CACHEDIR
  IO.println "Compressing cache"
  let mut acc := default
  for (path, hash) in hashMap.toList do
    let zip := hash.asTarGz
    let zipPath := CACHEDIR / zip
    let buildPaths ← mkBuildPaths pkgDirs path
    if ← allExist buildPaths then
      if (overwrite || !(← zipPath.pathExists)) then
        discard $ runCmd "tar" $ #["-I", "gzip -9", "-cf", zipPath.toString] ++
          (buildPaths.map toString)
      acc := acc.push zip
  return acc

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO $ Lean.RBTree String compare := do
  let paths ← getFilesWithExtension CACHEDIR "gz"
  return .ofList (paths.data.map (·.withoutParent CACHEDIR |>.toString))

/-- Decompresses build files into their respective folders -/
def unpackCache (cfg : Config) (hashMap : HashMap) : IO Unit := do
  let hashMap := hashMap.filter (← getLocalCacheSet) true
  let size := hashMap.size
  if size == 0 then IO.println "No cache files to decompress"
  else
    IO.println s!"Decompressing {size} file(s)"
    let rootDirStr := cfg.rootDir.toString
    hashMap.forM fun path hash => do
      match path.parent with
      | none | some path => do
        let pkgDir ← getPackageDir cfg.pkgDirs path
        mkDir $ pkgDir / LIBDIR / path
        mkDir $ pkgDir / IRDIR / path
        if rootDirStr != "." && cfg.rootDir == pkgDir then
          discard $ runCmd "tar" #["-xzf", s!"{CACHEDIR / hash.asTarGz}", "-C", rootDirStr]
        else
          discard $ runCmd "tar" #["-xzf", s!"{CACHEDIR / hash.asTarGz}"]

/-- Retrieves the azure token from the environment -/
def getToken (tokenEnvVar : String) : IO String := do
  let some token ← IO.getEnv tokenEnvVar
    | throw $ IO.userError s!"environment variable {tokenEnvVar} must be set to upload caches"
  return token

instance : Ord FilePath where
  compare x y := compare x.toString y.toString

/-- Removes all cache files except for what's in the `keep` set -/
def cleanCache (keep : Lean.RBTree FilePath compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "gz" do
    if ! keep.contains path then IO.FS.removeFile path

end Cache.IO
