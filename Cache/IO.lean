/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster
-/

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
def isInLeanCore (mod : Name) := #[
  `Init,
  `Lean,
  `Std,
  `Lake ].contains mod.getRoot

/-- Determine if the package `mod` is part of the mathlib cache.

TODO: write a better predicate. -/
def isPartOfMathlibCache (mod : Name) : Bool := #[
  `Mathlib,
  `Batteries,
  `Aesop,
  `Cli,
  `ImportGraph,
  `LeanSearchClient,
  `Plausible,
  `Qq,
  `ProofWidgets,
  `Archive,
  `Counterexamples,
  `MathlibTest ].contains mod.getRoot

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
  paths to the source directory of each imported package, i.e. where the `.lean` files
  can be found.
  (Note: in a standard setup these might also be the paths where the correpsponding `.lake`
  folders are located. However, `lake` has multiple options to customise these paths, like
  setting `srcDir` in a `lean_lib`. See `mkBuildPaths` below which currently assumes
  that no such options are set in any mathlib dependency)
* the build directory for proofwidgets
-/
structure CacheM.Context where
  /-- source directory for mathlib files -/
  mathlibDepPath : FilePath
  /-- the Lean source search path -/
  srcSearchPath : SearchPath
  /-- build directory for proofwidgets -/
  proofWidgetsBuildDir : FilePath

@[inherit_doc CacheM.Context]
abbrev CacheM := ReaderT CacheM.Context IO

/-- Whether this is running on Mathlib repo or not -/
def isMathlibRoot : IO Bool :=
  FilePath.mk "Mathlib" |>.pathExists

section

/-- Find path to `Mathlib` source directory -/
private def CacheM.mathlibDepPath (sp : SearchPath) : IO FilePath := do
  let mathlibSourceFile ← Lean.findLean sp `Mathlib
  let some mathlibSource ← pure mathlibSourceFile.parent
    | throw <| IO.userError s!"Mathlib not found in dependencies"
  return mathlibSource

private def CacheM.getContext : IO CacheM.Context := do
  let sp ← initSrcSearchPath
  let mathlibSource ← CacheM.mathlibDepPath sp
  return {
    mathlibDepPath := mathlibSource,
    srcSearchPath := sp,
    proofWidgetsBuildDir := LAKEPACKAGESDIR / "proofwidgets" / ".lake" / "build"}

/-- Run a `CacheM` in `IO` by loading the context from `LEAN_SRC_PATH`. -/
def CacheM.run (f : CacheM α) : IO α := do ReaderT.run f (← getContext)

end

/--
`mod` is assumed to be the module name like `Mathlib.Init`.

Find the source directory for `mod`.
This corresponds to the folder where the `.lean` files are located, i.e. for `Mathlib.Init`,
the file should be located at `(← getSrcDir _) / "Mathlib" / "Init.lean`.

Usually it is either `.` or something like `./.lake/packages/mathlib/`
-/
def getSrcDir (mod : Name) : CacheM FilePath := do
  let sp := (← read).srcSearchPath

  let .some srcDir ← sp.findWithExtBase "lean" mod |
    throw <| IO.userError s!"Unknown package directory for {mod}\nsearch paths: {sp}"

  return srcDir

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
Given a module name, concatenates the paths to its build files.
Each build file also has a `Bool` indicating whether that file is required for caching to proceed.
-/
def mkBuildPaths (mod : Name) : CacheM <| List (FilePath × Bool) := do
  /-
  TODO: if `srcDir` or other custom lake layout options are set in the `lean_lib`,
  `packageSrcDir / LIBDIR` might be the wrong path!

  See [Lake documentation](https://github.com/leanprover/lean4/tree/master/src/lake#layout)
  for available options.

  If a dependency is added to mathlib which uses such a custom layout, `mkBuildPaths`
  needs to be adjusted!
  -/
  let packageDir ← getSrcDir mod
  let path := (System.mkFilePath <| mod.components.map toString)
  if !(← (packageDir / ".lake").isDir) then
    IO.eprintln <| s!"Warning: {packageDir / ".lake"} seems not to exist, most likely `cache` \
      will not work as expected!"

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
def packCache (hashMap : ModuleHashMap) (overwrite verbose unpackedOnly : Bool)
    (comment : Option String := none) :
    CacheM <| Array String := do
  IO.FS.createDirAll CACHEDIR
  IO.println "Compressing cache"
  let sp := (← read).srcSearchPath
  let mut acc := #[]
  let mut tasks := #[]
  for (mod, hash) in hashMap.toList do
    let sourceFile ← Lean.findLean sp mod
    let zip := hash.asLTar
    let zipPath := CACHEDIR / zip
    let buildPaths ← mkBuildPaths mod
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

def isFromMathlib (mod : Name) : Bool :=
  mod.getRoot == `Mathlib

/-- Decompresses build files into their respective folders -/
def unpackCacheSingle (cacheFile : String) (pkgDir : String) (force : Bool) : IO Unit := do
  let args := (if force then #["-f"] else #[]) ++ #["-x", "--delete-corrupted", "-j", "-"]
  let child ← IO.Process.spawn { cmd := ← getLeanTar, args, stdin := .piped }
  let (stdin, child) ← child.takeStdin
  -- let pathStr := s!"{CACHEDIR / hash.asLTar}"
  let config : Array Lean.Json := #[.mkObj [("file", cacheFile), ("base", pkgDir)]]
  stdin.putStr <| Lean.Json.compress <| .arr config
  let exitCode ← child.wait
  if exitCode != 0 then throw <| IO.userError s!"leantar failed with error code {exitCode}"

/-- Decompresses build files into their respective folders -/
def unpackCache (hashMap : ModuleHashMap) (force : Bool) : CacheM Unit := do
  let hashMap ← hashMap.filterExists true
  let size := hashMap.size
  if size > 0 then
    let now ← IO.monoMsNow
    IO.println s!"Decompressing remaining {size} file(s)"
    let args := (if force then #["-f"] else #[]) ++ #["-x", "--delete-corrupted", "-j", "-"]
    let child ← IO.Process.spawn { cmd := ← getLeanTar, args, stdin := .piped }
    let (stdin, child) ← child.takeStdin
    /-
    TODO: The case distinction below could be avoided by making use of the `leantar` option `-C`
    (rsp the `"base"` field in JSON format, see below) here and in `packCache`.

    See also https://github.com/leanprover-community/mathlib4/pull/8767#discussion_r1422077498

    Doing this, one could avoid that the package directory path (for dependencies) appears
    inside the leantar files, but unless `cache` is upstreamed to work on upstream packages
    themselves (without `Mathlib`), this might not be too useful to change.

    NOTE: making changes to the generated .ltar files invalidates them while it *DOES NOT* change
    the file hash! This means any such change needs to be accompanied by a change
    to the root hash affecting *ALL* files
    (e.g. any modification to lakefile, lean-toolchain or manifest)
    -/
    let isMathlibRoot ← isMathlibRoot
    let mathlibDepPath := (← read).mathlibDepPath.toString
    let config : Array Lean.Json := hashMap.fold (init := #[]) fun config mod hash =>
      let pathStr := s!"{CACHEDIR / hash.asLTar}"
      if isMathlibRoot || !isFromMathlib mod then
        config.push <| .str pathStr
      else
        -- only mathlib files, when not in the mathlib4 repo, need to be redirected
        config.push <| .mkObj [("file", pathStr), ("base", mathlibDepPath)]
    stdin.putStr <| Lean.Json.compress <| .arr config
    let exitCode ← child.wait
    if exitCode != 0 then throw <| IO.userError s!"leantar failed with error code {exitCode}"
    IO.println s!"Unpacked remaining in {(← IO.monoMsNow) - now} ms"

instance : Ord FilePath where
  compare x y := compare x.toString y.toString

/-- Removes all cache files except for what's in the `keep` set -/
def cleanCache (keep : Lean.RBTree FilePath compare := ∅) : IO Unit := do
  for path in ← getFilesWithExtension CACHEDIR "ltar" do
    if !keep.contains path then IO.FS.removeFile path

/-- Prints the LTAR file and embedded comments (in particular, the mathlib commit that built the
file) regarding the specified modules. -/
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
Position `0` (i.e. the command `get`, `clean`, etc.) is ignored.
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
    let sp := (← read).srcSearchPath
    args₀.foldlM (init := ∅) fun acc (argₛ : String) => do
      let arg : FilePath := argₛ
      if arg.components.length > 1 || arg.extension == "lean" then
        -- provided file name of a Lean file
        let mod : Name := arg.withExtension "" |>.components.foldl .str .anonymous
        let srcDir ← getSrcDir mod
        if !(← arg.pathExists) then
          IO.eprintln s!"Invalid argument: non-existing path {arg}"
          IO.Process.exit 1
        if arg.extension == "lean" then
          -- provided existing `.lean` file
          pure <| acc.insert mod argₛ
        else
          -- provided existing directory: walk it
          IO.println s!"Searching directory {arg} for .lean files"
          let leanModulesInFolder ← walkDir arg srcDir
          pure <| acc.insertMany leanModulesInFolder
      else
        -- provided a module
        let mod := argₛ.toName
        let srcDir ← getSrcDir mod
        let sourceFile ← Lean.findLean sp mod

        if ← sourceFile.pathExists then
          -- provided valid module
          pure <| acc.insert mod sourceFile
        else
          -- provided "pseudo-module" like `Mathlib.Data` which
          -- does not correspond to a Lean file, but to an existing folder
          -- `Mathlib/Data/`
          let folder := sourceFile.withExtension ""
          IO.println s!"Searching directory {folder} for .lean files"
          if ← folder.pathExists then
            -- provided "module name" of an existing folder: walk dir
            let leanModulesInFolder ← walkDir folder srcDir
            pure <| acc.insertMany leanModulesInFolder
          else
            IO.eprintln s!"Invalid argument: non-existing module {mod}"
            IO.Process.exit 1
where
  /-- assumes the folder exists -/
  walkDir (folder : FilePath) (srcDir : FilePath) : CacheM <| Array (Name × FilePath) := do
    -- find all Lean files in the folder, skipping hidden folders/files
    let files ← folder.walkDir fun p => match p.fileName with
      | some s => pure <| !(s.startsWith ".")
      | none => pure false
    let leanFiles := files.filter (·.extension == some "lean")
    let mut leanModulesInFolder : Array (Name × FilePath) := #[]
    for file in leanFiles do
      let path := file.withoutParent srcDir
      let mod : Name := path.withExtension "" |>.components.foldl .str .anonymous
      leanModulesInFolder := leanModulesInFolder.push (mod, file)
    pure leanModulesInFolder

end Cache.IO
