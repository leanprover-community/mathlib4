/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean.Data.HashMap
import Lean.Data.RBMap
import Lean.Data.RBTree
import Lean.Data.Json.Printer

set_option autoImplicit true

/-- Removes a parent path from the beginning of a path -/
def System.FilePath.withoutParent (path parent : FilePath) : FilePath :=
  let rec aux : List String → List String → List String
    | z@(x :: xs), y :: ys => if x == y then aux xs ys else z
    | [], _ => []
    | x, [] => x
  mkFilePath $ aux path.components parent.components

def Nat.toHexDigits (n : Nat) : Nat → (res : String := "") → String
  | 0, s => s
  | len+1, s =>
    let b := UInt8.ofNat (n >>> (len * 8))
    Nat.toHexDigits n len <|
      s.push (Nat.digitChar (b >>> 4).toNat) |>.push (Nat.digitChar (b &&& 15).toNat)

def UInt64.asLTar (n : UInt64) : String :=
  s!"{Nat.toHexDigits n.toNat 8}.ltar"

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
  | some path => return path / "mathlib"
  | none =>
    let home ← if System.Platform.isWindows then
      let drive ← IO.getEnv "HOMEDRIVE"
      let path ← IO.getEnv "HOMEPATH"
      pure <| return (← drive) ++ (← path)
    else IO.getEnv "HOME"
    match home with
    | some path => return path / ".cache" / "mathlib"
    | none => pure ⟨".cache"⟩

/-- Target file path for `curl` configurations -/
def CURLCFG :=
  IO.CACHEDIR / "curl.cfg"

/-- curl version at https://github.com/leanprover-community/static-curl -/
def CURLVERSION :=
  "7.88.1"

def CURLBIN :=
  -- change file name if we ever need a more recent version to trigger re-download
  IO.CACHEDIR / s!"curl-{CURLVERSION}"

/-- leantar version at https://github.com/digama0/leangz -/
def LEANTARVERSION :=
  "0.1.7"

def EXE := if System.Platform.isWindows then ".exe" else ""

def LEANTARBIN :=
  -- change file name if we ever need a more recent version to trigger re-download
  IO.CACHEDIR / s!"leantar-{LEANTARVERSION}{EXE}"

def LAKEPACKAGESDIR : FilePath :=
  ⟨"lake-packages"⟩

def getCurl : IO String := do
  return if (← CURLBIN.pathExists) then CURLBIN.toString else "curl"

def getLeanTar : IO String := do
  return if (← LEANTARBIN.pathExists) then LEANTARBIN.toString else "leantar"

abbrev PackageDirs := Lean.RBMap String FilePath compare

/-- Whether this is running on Mathlib repo or not -/
def isMathlibRoot : IO Bool :=
  FilePath.mk "Mathlib" |>.pathExists

def mathlibDepPath : FilePath :=
  LAKEPACKAGESDIR / "mathlib"

-- TODO this should be generated automatically from the information in `lakefile.lean`.
def getPackageDirs : IO PackageDirs := return .ofList [
  ("Mathlib", if ← isMathlibRoot then "." else mathlibDepPath),
  ("MathlibExtras", if ← isMathlibRoot then "." else mathlibDepPath),
  ("Archive", if ← isMathlibRoot then "." else mathlibDepPath),
  ("Counterexamples", if ← isMathlibRoot then "." else mathlibDepPath),
  ("Aesop", LAKEPACKAGESDIR / "aesop"),
  ("Std", LAKEPACKAGESDIR / "std"),
  ("Cli", LAKEPACKAGESDIR / "Cli"),
  ("ProofWidgets", LAKEPACKAGESDIR / "proofwidgets"),
  ("Qq", LAKEPACKAGESDIR / "Qq")
]

initialize pkgDirs : PackageDirs ← getPackageDirs

def getPackageDir (path : FilePath) : IO FilePath :=
  match path.withExtension "" |>.components.head? with
  | none => throw $ IO.userError "Can't find package directory for empty path"
  | some pkg => match pkgDirs.find? pkg with
    | none => throw $ IO.userError s!"Unknown package directory for {pkg}"
    | some path => return path

/-- Runs a terminal command and retrieves its output, passing the lines to `processLine` -/
partial def runCurlStreaming (args : Array String) (init : α)
    (processLine : α → String → IO α) : IO α := do
  let child ← IO.Process.spawn { cmd := ← getCurl, args, stdout := .piped, stderr := .piped }
  loop child.stdout init
where
  loop (h : IO.FS.Handle) (a : α) : IO α := do
    let line ← h.getLine
    if line.isEmpty then
      return a
    else
      loop h (← processLine a line)

/-- Runs a terminal command and retrieves its output -/
def runCmd (cmd : String) (args : Array String) (throwFailure := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 && throwFailure then throw $ IO.userError out.stderr
  else return out.stdout

def runCurl (args : Array String) (throwFailure := true) : IO String := do
  runCmd (← getCurl) args throwFailure

def validateCurl : IO Bool := do
  if (← CURLBIN.pathExists) then return true
  match (← runCmd "curl" #["--version"]).splitOn " " with
  | "curl" :: v :: _ => match v.splitOn "." with
    | maj :: min :: _ =>
      let version := (maj.toNat!, min.toNat!)
      let _ := @lexOrd
      let _ := @leOfOrd
      if version >= (7, 81) then return true
      -- TODO: support more platforms if the need arises
      let arch ← (·.trim) <$> runCmd "uname" #["-m"] false
      let kernel ← (·.trim) <$> runCmd "uname" #["-s"] false
      if kernel == "Linux" && arch ∈ ["x86_64", "aarch64"] then
        IO.println s!"curl is too old; downloading more recent version"
        IO.FS.createDirAll IO.CACHEDIR
        let _ ← runCmd "curl" #[
          s!"https://github.com/leanprover-community/static-curl/releases/download/v{CURLVERSION}/curl-{arch}-linux-static",
          "-L", "-o", CURLBIN.toString]
        let _ ← runCmd "chmod" #["u+x", CURLBIN.toString]
        return true
      if version >= (7, 70) then
        IO.println s!"Warning: recommended `curl` version ≥7.81. Found {v}"
        return true
      else
        IO.println s!"Warning: recommended `curl` version ≥7.70. Found {v}. Can't use `--parallel`."
        return false
    | _ => throw $ IO.userError "Invalidly formatted version of `curl`"
  | _ => throw $ IO.userError "Invalidly formatted response from `curl --version`"

def Version := Nat × Nat × Nat
  deriving Inhabited, DecidableEq

instance : Ord Version := let _ := @lexOrd; lexOrd
instance : LE Version := leOfOrd

def parseVersion (s : String) : Option Version := do
  let [maj, min, patch] := s.splitOn "." | none
  some (maj.toNat!, min.toNat!, patch.toNat!)

def validateLeanTar : IO Unit := do
  if (← LEANTARBIN.pathExists) then return
  if let some version ← some <$> runCmd "leantar" #["--version"] <|> pure none then
    let "leantar" :: v :: _ := version.splitOn " "
      | throw $ IO.userError "Invalidly formatted response from `leantar --version`"
    let some v := parseVersion v | throw $ IO.userError "Invalidly formatted version of `leantar`"
    -- currently we need exactly one version of leantar, change this to reflect compatibility
    if v = (parseVersion LEANTARVERSION).get! then return
  let win := System.Platform.getIsWindows ()
  let target ← if win then
    pure "x86_64-pc-windows-msvc"
  else
    let mut arch ← (·.trim) <$> runCmd "uname" #["-m"] false
    if arch = "arm64" then arch := "aarch64"
    unless arch ∈ ["x86_64", "aarch64"] do
      throw $ IO.userError s!"unsupported architecture {arch}"
    pure <|
      if System.Platform.getIsOSX () then s!"{arch}-apple-darwin"
      else s!"{arch}-unknown-linux-musl"
  IO.println s!"leantar is too old; downloading more recent version"
  IO.FS.createDirAll IO.CACHEDIR
  let ext := if win then "zip" else "tar.gz"
  let _ ← runCmd "curl" #[
    s!"https://github.com/digama0/leangz/releases/download/v{LEANTARVERSION}/leantar-v{LEANTARVERSION}-{target}.{ext}",
    "-L", "-o", s!"{LEANTARBIN}.{ext}"]
  let _ ← runCmd "tar" #["-xf", s!"{LEANTARBIN}.{ext}",
    "-C", IO.CACHEDIR.toString, "--strip-components=1"]
  IO.FS.rename (IO.CACHEDIR / s!"leantar{EXE}").toString LEANTARBIN.toString

/-- Recursively gets all files from a directory with a certain extension -/
partial def getFilesWithExtension
  (fp : FilePath) (extension : String) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getFilesWithExtension dir.path extension acc) acc
  else return if fp.extension == some extension then acc.push fp else acc

abbrev HashMap := Lean.HashMap FilePath UInt64

namespace HashMap

/-- Filter the hashmap by whether the entries exist as files in the cache directory.

If `keep` is true, the result will contain the entries that do exist;
if `keep` is false, the result will contain the entries that do not exist.
-/
def filterExists (hashMap : HashMap) (keep : Bool) : IO HashMap :=
  hashMap.foldM (init := default) fun acc path hash => do
    let exist ← (CACHEDIR / hash.asLTar).pathExists
    let add := if keep then exist else !exist
    if add then return acc.insert path hash else return acc

def hashes (hashMap : HashMap) : Lean.RBTree UInt64 compare :=
  hashMap.fold (init := default) fun acc _ hash => acc.insert hash

end HashMap

def mkDir (path : FilePath) : IO Unit := do
  if !(← path.pathExists) then IO.FS.createDirAll path

/--
Given a path to a Lean file, concatenates the paths to its build files.
Each build file also has a `Bool` indicating whether that file is required for caching to proceed.
-/
def mkBuildPaths (path : FilePath) : IO $ List (FilePath × Bool) := do
  let packageDir ← getPackageDir path
  return [
    -- Note that `packCache` below requires that the `.trace` file is first in this list.
    (packageDir / LIBDIR / path.withExtension "trace", true),
    (packageDir / LIBDIR / path.withExtension "olean", true),
    (packageDir / LIBDIR / path.withExtension "olean.hash", true),
    (packageDir / LIBDIR / path.withExtension "ilean", true),
    (packageDir / LIBDIR / path.withExtension "ilean.hash", true),
    (packageDir / IRDIR  / path.withExtension "c", true),
    (packageDir / IRDIR  / path.withExtension "c.hash", true),
    (packageDir / LIBDIR / path.withExtension "extra", false)]

/-- Check that all required build files exist. -/
def allExist (paths : List (FilePath × Bool)) : IO Bool := do
  for (path, required) in paths do
    if required then if !(← path.pathExists) then return false
  pure true

/-- Compresses build files into the local cache and returns an array with the compressed files -/
def packCache (hashMap : HashMap) (overwrite : Bool) (comment : Option String := none) :
    IO $ Array String := do
  mkDir CACHEDIR
  IO.println "Compressing cache"
  let mut acc := #[]
  let mut tasks := #[]
  for (path, hash) in hashMap.toList do
    let zip := hash.asLTar
    let zipPath := CACHEDIR / zip
    let buildPaths ← mkBuildPaths path
    if ← allExist buildPaths then
      if overwrite || !(← zipPath.pathExists) then
        tasks := tasks.push <| ← IO.asTask do
          -- Note here we require that the `.trace` file is first
          -- in the list generated by `mkBuildPaths`.
          let trace :: args := (← buildPaths.filterM (·.1.pathExists)) |>.map (·.1.toString)
            | unreachable!
          runCmd (← getLeanTar) $ #[zipPath.toString, trace] ++
            (if let some c := comment then #["-c", s!"git=mathlib4@{c}"] else #[]) ++ args
      acc := acc.push zip
  for task in tasks do
    _ ← IO.ofExcept task.get
  return acc

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO $ Lean.RBTree String compare := do
  let paths ← getFilesWithExtension CACHEDIR "ltar"
  return .fromList (paths.data.map (·.withoutParent CACHEDIR |>.toString)) _

def isPathFromMathlib (path : FilePath) : Bool :=
  match path.components with
  | "Mathlib" :: _ => true
  | ["Mathlib.lean"] => true
  | "MathlibExtras" :: _ => true
  | ["MathlibExtras.lean"] => true
  | _ => false

/-- Decompresses build files into their respective folders -/
def unpackCache (hashMap : HashMap) (force : Bool) : IO Unit := do
  let hashMap ← hashMap.filterExists true
  let size := hashMap.size
  if size > 0 then
    let now ← IO.monoMsNow
    IO.println s!"Decompressing {size} file(s)"
    let isMathlibRoot ← isMathlibRoot
    let args := (if force then #["-f"] else #[]) ++ #["-x", "-j", "-"]
    let child ← IO.Process.spawn { cmd := ← getLeanTar, args, stdin := .piped }
    let (stdin, child) ← child.takeStdin
    let config : Array Lean.Json := hashMap.fold (init := #[]) fun config path hash =>
      let pathStr := s!"{CACHEDIR / hash.asLTar}"
      if isMathlibRoot || !isPathFromMathlib path then
        config.push <| .str pathStr
      else -- only mathlib files, when not in the mathlib4 repo, need to be redirected
        config.push <| .mkObj [("file", pathStr), ("base", mathlibDepPath.toString)]
    stdin.putStr <| Lean.Json.compress <| .arr config
    let exitCode ← child.wait
    if exitCode != 0 then throw $ IO.userError s!"leantar failed with error code {exitCode}"
    IO.println s!"unpacked in {(← IO.monoMsNow) - now} ms"
  else IO.println "No cache files to decompress"

/-- Retrieves the azure token from the environment -/
def getToken : IO String := do
  let some token ← IO.getEnv "MATHLIB_CACHE_SAS"
    | throw $ IO.userError "environment variable MATHLIB_CACHE_SAS must be set to upload caches"
  return token

instance : Ord FilePath where
  compare x y := compare x.toString y.toString

/-- Removes all cache files except for what's in the `keep` set -/
def cleanCache (keep : Lean.RBTree FilePath compare := default) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "ltar" do
    if !keep.contains path then IO.FS.removeFile path

end Cache.IO
