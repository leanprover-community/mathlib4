/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster
-/

import Lean.Data.Json.Printer
import Cache.Lean

variable {α : Type}

open Lean

namespace Cache.IO

open System (FilePath)

/-- Target directory for build files -/
def LIBDIR : FilePath :=
  ".lake" / "build" / "lib"

/-- Target directory for IR files -/
def IRDIR : FilePath :=
  ".lake" / "build" / "ir"

/--
TODO: is there a better test to see if a module is part of Lean core?
-/
def isInLeanCore (mod : Name) :=
  #[`Init, `Lean, `Std, `Lake].contains mod.getRoot

/--
TODO: write a better test which modules are part of the mathlib cache
-/
def isPartOfMathlibCache (mod : Name) :=
  #[`Mathlib, `Batteries, `Aesop, `Cli, `ImportGraph,
    `LeanSearchClient, `Plausible, `Qq, `ProofWidgets,
    `Archive, `Counterexamples, `MathlibTest].contains mod.getRoot

/-- Target directory for caching -/
initialize CACHEDIR : FilePath ← do
  match ← IO.getEnv "MATHLIB_CACHE_DIR" with
  | some path => return path
  | none =>
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
  "0.1.14"

def EXE := if System.Platform.isWindows then ".exe" else ""

def LEANTARBIN :=
  -- change file name if we ever need a more recent version to trigger re-download
  IO.CACHEDIR / s!"leantar-{LEANTARVERSION}{EXE}"

def LAKEPACKAGESDIR : FilePath :=
  ".lake" / "packages"

def getCurl : IO String := do
  return if (← CURLBIN.pathExists) then CURLBIN.toString else "curl"

def getLeanTar : IO String := do
  return if (← LEANTARBIN.pathExists) then LEANTARBIN.toString else "leantar"

/--
`CacheM` stores the following information:
* the source directory where `Mathlib.lean` lies
* the Lean search path. This contains
  paths to the source directory of each imported package. The build files (e.g. `.olean`)
  of a package should then be in a `.lake`-folder inside this root directory
  (see `LIBDIR` and `IRDIR`).
* the build directory for proofwidgets
-/
structure CacheM.Context where
  /-- source directory for mathlib files -/
  mathlibDepPath : FilePath
  /-- the Lean search path -/
  searchPath : SearchPath
  /-- build directory for proofwidgets -/
  proofWidgetsBuildDir : FilePath

@[inherit_doc CacheM.Context]
abbrev CacheM := ReaderT CacheM.Context IO

section

@[inherit_doc CacheM.Context]
private def CacheM.getContext : IO CacheM.Context := do
  let sp ← initSrcSearchPath
  let mathlibSourceFile ← Lean.findLean sp `Mathlib
  let some mathlibSource ← pure mathlibSourceFile.parent
    | throw <| IO.userError s!"Mathlib not found in dependencies"
  return {
    mathlibDepPath := mathlibSource
    searchPath := sp
    proofWidgetsBuildDir := LAKEPACKAGESDIR / "proofwidgets" / ".lake" / "build" }

@[inherit_doc CacheM.Context]
def CacheM.run (f : CacheM α) : IO α := do ReaderT.run f (← getContext)

end

/--
Get the correct package directory the file `sourceFile`.

Basically, this is just a parent of `sourceFile`, but this function determines how
many components of the path `sourceFile` make up the package directory.
-/
def getPackageDir (sourceFile : FilePath) : CacheM FilePath := do
  let sp := (← read).searchPath
  -- Note: This seems to work since the path `.` is listed last, so it will not be found unless
  -- no other search-path applies. Could be more robust.
  let packageDir? := sp.find? (·.contains sourceFile)
  match packageDir? with
  | some dir => return dir
  | none => throw <| IO.userError s!"Unknown package directory for {sourceFile}\nsearch paths: {sp}"

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
def runCmd (cmd : String) (args : Array String) (throwFailure stderrAsErr := true) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if (out.exitCode != 0 || stderrAsErr && !out.stderr.isEmpty) && throwFailure then
    throw <| IO.userError s!"failure in {cmd} {args}:\n{out.stderr}"
  else if !out.stderr.isEmpty then
    IO.eprintln out.stderr
  return out.stdout

def runCurl (args : Array String) (throwFailure stderrAsErr := true) : IO String := do
  runCmd (← getCurl) (#["--no-progress-meter"] ++ args) throwFailure stderrAsErr

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
        let _ ← runCmd "curl" (stderrAsErr := false) #[
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
    | _ => throw <| IO.userError "Invalidly formatted version of `curl`"
  | _ => throw <| IO.userError "Invalidly formatted response from `curl --version`"

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
      | throw <| IO.userError "Invalidly formatted response from `leantar --version`"
    let some v := parseVersion v | throw <| IO.userError "Invalidly formatted version of `leantar`"
    -- currently we need exactly one version of leantar, change this to reflect compatibility
    if v = (parseVersion LEANTARVERSION).get! then return
  let win := System.Platform.getIsWindows ()
  let target ← if win then
    pure "x86_64-pc-windows-msvc"
  else
    let mut arch ← (·.trim) <$> runCmd "uname" #["-m"] false
    if arch = "arm64" then arch := "aarch64"
    unless arch ∈ ["x86_64", "aarch64"] do
      throw <| IO.userError s!"unsupported architecture {arch}"
    pure <|
      if System.Platform.getIsOSX () then s!"{arch}-apple-darwin"
      else s!"{arch}-unknown-linux-musl"
  IO.println s!"installing leantar {LEANTARVERSION}"
  IO.FS.createDirAll IO.CACHEDIR
  let ext := if win then "zip" else "tar.gz"
  let _ ← runCmd "curl" (stderrAsErr := false) #[
    s!"https://github.com/digama0/leangz/releases/download/v{LEANTARVERSION}/leantar-v{LEANTARVERSION}-{target}.{ext}",
    "-L", "-o", s!"{LEANTARBIN}.{ext}"]
  let _ ← runCmd "tar" #["-xf", s!"{LEANTARBIN}.{ext}",
    "-C", IO.CACHEDIR.toString, "--strip-components=1"]
  IO.FS.rename (IO.CACHEDIR / s!"leantar{EXE}").toString LEANTARBIN.toString

/-- Recursively gets all files from a directory with a certain extension -/
partial def getFilesWithExtension
  (fp : FilePath) (extension : String) (acc : Array FilePath := #[]) :
    IO <| Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getFilesWithExtension dir.path extension acc) acc
  else return if fp.extension == some extension then acc.push fp else acc

/--
The Hash map of the cache.
-/
abbrev ModuleHashMap := Std.HashMap Name UInt64

namespace ModuleHashMap

/-- Filter the hashmap by whether the entries exist as files in the cache directory.

If `keep` is true, the result will contain the entries that do exist;
if `keep` is false, the result will contain the entries that do not exist.
-/
def filterExists (hashMap : ModuleHashMap) (keep : Bool) : IO ModuleHashMap :=
  hashMap.foldM (init := ∅) fun acc mod hash => do
    let exist ← (CACHEDIR / hash.asLTar).pathExists
    let add := if keep then exist else !exist
    if add then return acc.insert mod hash else return acc

def hashes (hashMap : ModuleHashMap) : Lean.RBTree UInt64 compare :=
  hashMap.fold (init := ∅) fun acc _ hash => acc.insert hash

end ModuleHashMap

/--
Given a path to a Lean file, concatenates the paths to its build files.
Each build file also has a `Bool` indicating whether that file is required for caching to proceed.
-/
def mkBuildPaths (mod : Name) (sourceFile : FilePath) : CacheM <| List (FilePath × Bool) := do
  let packageDir ← getPackageDir sourceFile
  let path := (System.mkFilePath <| mod.components.map toString)
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
def packCache (hashMap : ModuleHashMap) (pathMap : Std.HashMap Name FilePath)
    (overwrite verbose unpackedOnly : Bool) (comment : Option String := none) :
    CacheM <| Array String := do
  IO.FS.createDirAll CACHEDIR
  IO.println "Compressing cache"
  let mut acc := #[]
  let mut tasks := #[]
  for (mod, hash) in hashMap.toList do
    let sourceFile := pathMap.get! mod
    let zip := hash.asLTar
    let zipPath := CACHEDIR / zip
    let buildPaths ← mkBuildPaths mod sourceFile
    if ← allExist buildPaths then
      if overwrite || !(← zipPath.pathExists) then
        acc := acc.push (sourceFile, zip)
        tasks := tasks.push <| ← IO.asTask do
          -- Note here we require that the `.trace` file is first
          -- in the list generated by `mkBuildPaths`.
          let trace :: args := (← buildPaths.filterM (·.1.pathExists)) |>.map (·.1.toString)
            | unreachable!
          runCmd (← getLeanTar) <| #[zipPath.toString, trace] ++
            (if let some c := comment then #["-c", s!"git=mathlib4@{c}"] else #[]) ++ args
      else if !unpackedOnly then
        acc := acc.push (sourceFile, zip)
  for task in tasks do
    _ ← IO.ofExcept task.get
  acc := acc.qsort (·.1.1 < ·.1.1)
  if verbose then
    for (path, zip) in acc do
      println! "packing {path} as {zip}"
  return acc.map (·.2)

/-- Gets the set of all cached files -/
def getLocalCacheSet : IO <| Lean.RBTree String compare := do
  let paths ← getFilesWithExtension CACHEDIR "ltar"
  return .fromList (paths.toList.map (·.withoutParent CACHEDIR |>.toString)) _

/-- Decompresses build files into their respective folders -/
def unpackCache (hashMap : ModuleHashMap) (pathMap : Std.HashMap Name FilePath) (force : Bool) : CacheM Unit := do
  let hashMap ← hashMap.filterExists true
  let size := hashMap.size
  if size > 0 then
    let now ← IO.monoMsNow
    IO.println s!"Decompressing {size} file(s)"
    let args := (if force then #["-f"] else #[]) ++ #["-x", "--delete-corrupted", "-j", "-"]
    let child ← IO.Process.spawn { cmd := ← getLeanTar, args, stdin := .piped }
    let (stdin, child) ← child.takeStdin
    let config : Array Lean.Json ← hashMap.foldM (init := #[]) fun config mod hash => do
      let pathStr := s!"{CACHEDIR / hash.asLTar}"
      -- TODO: We could do this with `pkgDir` for all modules, not only ones in mathlib.
      -- This would be more flexible and allow cached dependencies to live somewhere else (locally).
      -- However, this change invalidates existing .ltar files, so it needs
      -- to be accompanied with some hash change.
      -- In practice, cached local mathlib dependencies would lead to a new `rootHash` anyways
      -- (mathllib lakefile/manifest would need to reflect this) and therefore would
      -- invalidate cache anyways, therefore we leave it as is.
      -- see: https://github.com/leanprover-community/mathlib4/pull/8767#discussion_r1422077498
      if mod.getRoot == `Mathlib then
        -- only mathlib files, when not in the mathlib4 repo, need to be redirected
        let sourceFile := pathMap[mod]!
        let pkgDir := (← getPackageDir sourceFile).toString
        pure <| config.push <| .mkObj [("file", pathStr), ("base", pkgDir)]
      else
        pure <| config.push <| .str pathStr
    stdin.putStr <| Lean.Json.compress <| .arr config
    let exitCode ← child.wait
    if exitCode != 0 then throw <| IO.userError s!"leantar failed with error code {exitCode}"
    IO.println s!"Unpacked in {(← IO.monoMsNow) - now} ms"
    IO.println "Completed successfully!"
  else IO.println "No cache files to decompress"

instance : Ord FilePath where
  compare x y := compare x.toString y.toString

/-- Removes all cache files except for what's in the `keep` set -/
def cleanCache (keep : Lean.RBTree FilePath compare := ∅) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "ltar" do
    if !keep.contains path then IO.FS.removeFile path

/-- Prints the LTAR file and embedded comments (in particular, the mathlib commit that built the
file) regarding the files with specified paths. -/
def lookup (hashMap : ModuleHashMap) (modules : List Name) : IO Unit := do
  let mut err := false
  for mod in modules do
    let some hash := hashMap[mod]? | err := true
    let ltar := CACHEDIR / hash.asLTar
    IO.println s!"{mod}: {ltar}"
    for line in (← runCmd (← getLeanTar) #["-k", ltar.toString]).splitOn "\n" |>.dropLast do
      println! "  comment: {line}"
  if err then IO.Process.exit 1

/--
Parse command line arguments.
Position `0`, the command like [`get`, `clean`, etc.] is ignored.
The remaining arguments take one of the following forms:
1. `Mathlib.Algebra.Fields.Basic`: there exists such a Lean file
2. `Mathlib.Algebra.Fields`: no Lean file exists but a folder
3. `Mathlib/Algebra/Fields/Basic.lean`: the file exists (note potentially `\` on Windows)
4. `Mathlib/Algebra/Fields/`: the folder exists
5. (`Aesop/Builder.lean`: the file does not exist, it's
    actually somewhere in `.lake`. (not supported currently!))

An argument like `Archive` is treated as module, not a path.
-/
def parseArgs (args : List String) : CacheM <| Std.HashMap Name FilePath := do
  match args with
  | [] => pure ∅
  | _ :: args₀ =>
    let sp := (← read).searchPath
    args₀.foldlM (init := ∅) fun acc (arg : String) => do
      let arg' : FilePath := arg
      let mod : Name := arg'.withExtension "" |>.components.foldl .str .anonymous
      if arg'.components.length > 1 || arg'.extension == "lean" then
        -- provided file name of a Lean file
        if !(← arg'.pathExists) then
          IO.eprintln s!"Invalid argument: non-existing path {arg'}"
          IO.Process.exit 1
        if arg'.extension == "lean" then
          -- provided existing `.lean` file
          pure <| acc.insert mod arg
        else
          -- provided existing directory: walk it
          let leanModulesInFolder ← walkDir arg'
          pure <| acc.insertMany leanModulesInFolder
      else
        -- provided a module
        let mod := arg.toName
        let sourceFile ← Lean.findLean sp mod
        if ← sourceFile.pathExists then
          -- provided valid module
          pure <| acc.insert mod sourceFile
        else
          -- provided "pseudo-module" like `Mathlib.Data` which
          -- does not correspond to a Lean file, but to an existing folder
          -- `Mathlib/Data/`
          let folder := sourceFile.withExtension ""
          if ← folder.pathExists then
            -- case 2: "module name" of an existing folder: walk dir
            let leanModulesInFolder ← walkDir folder
            pure <| acc.insertMany leanModulesInFolder
          else
            IO.eprintln s!"Invalid argument: non-existing module {mod}"
            IO.Process.exit 1
where
  /-- assumes the folder exists -/
  walkDir (folder : FilePath) : CacheM <| Array (Name × FilePath) := do
    -- find all Lean files in the folder, skipping hidden folders/files
    let files ← folder.walkDir fun p => match p.fileName with
      | some s => pure <| !(s.startsWith ".")
      | none => pure false
    let leanFiles := files.filter (·.extension == some "lean")

    let mut leanModulesInFolder : Array (Name × FilePath) := #[]
    for file in leanFiles do
      let pkgDir ← getPackageDir file
      let path := file.withoutParent pkgDir
      let mod : Name := path.withExtension "" |>.components.foldl .str .anonymous
      leanModulesInFolder := leanModulesInFolder.push (mod, file)
    pure leanModulesInFolder

end Cache.IO
