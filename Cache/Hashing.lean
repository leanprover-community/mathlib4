/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.IO
import Lean.Elab.ParseImportsFast

namespace Cache.Hashing

open Lean IO
open System hiding SearchPath

/--
The `HashMemo` contains all information `Cache` needs about the modules:
* the name
* its imports
* the file's hash (in `hashMap` and `cache`)

additionally, it contains the `rootHash` which reflects changes to Mathlib's
Lake project settings.
-/
structure HashMemo where
  /-- Hash of mathlib's lake project settings. -/
  rootHash : UInt64
  /-- Maps the `.lean` file of a module to the `.lean` files of its imports. -/
  depsMap  : Std.HashMap FilePath (Array FilePath) := ∅
  /--
  For files with a valid hash (usually Mathlib and upstream),
  this contains the same information as `hashMap`.
  Other files have `none` here and do not appear in `hashMap`
  (e.g. `.lean` source could not be found, imports a file without valid hash).
  -/
  cache    : Std.HashMap FilePath (Option UInt64) := ∅
  /-- Stores the hash of the module's content for modules in Mathlib or upstream. -/
  hashMap  : ModuleHashMap := ∅
  deriving Inhabited

partial def insertDeps (hashMap : ModuleHashMap) (path : FilePath) (hashMemo : HashMemo) :
    ModuleHashMap :=
  if hashMap.contains path then hashMap else
  match (hashMemo.depsMap[path]?, hashMemo.hashMap[path]?) with
  | (some deps, some hash) => deps.foldl (insertDeps · · hashMemo) (hashMap.insert path hash)
  | _ => hashMap

/--
Filters the `hashMap` of a `HashMemo` so that it only contains key/value pairs such that every key:
* Belongs to the given list of file paths or
* Corresponds to a file that's imported (transitively of not) by some file in the list of file paths
-/
def HashMemo.filterByFilePaths (hashMemo : HashMemo) (filePaths : List FilePath) :
    IO ModuleHashMap := do
  let mut hashMap := ∅
  for filePath in filePaths do
    if hashMemo.hashMap.contains filePath then
      hashMap := insertDeps hashMap filePath hashMemo
    else IO.println s!"{filePath} is not covered by the olean cache."
  return hashMap

/-- We cache the hash of each file and their dependencies for later lookup -/
abbrev HashM := StateT HashMemo CacheM

/--
Read the imports from the raw file `content` and return an array of tuples
`(module name, source file)`, one per import.

Note: `fileName` is a string which is purely used for displaying an error message if
parsing imports from `content` should fail. It is intended to be the file's name.
-/
def getFileImports (content : String) (fileName : String := "") :
    CacheM <| Array (Name × FilePath) := do
  let sp := (← read).srcSearchPath
  let fileImports : Array Import ← Lean.parseImports' content fileName
  fileImports
    |>.filter (isPartOfMathlibCache ·.module)
    |>.mapM fun imp => do
      let impSourceFile ← Lean.findLean sp imp.module
      pure (imp.module, impSourceFile)

/-- Computes a canonical hash of a file's contents. -/
def hashFileContents (contents : String) : UInt64 :=
  -- revert potential file transformation by git's `autocrlf`
  hash contents.crlfToLf

/--
Computes the root hash, which mixes the hashes of the content of:
* `lakefile.lean`
* `lean-toolchain`
* `lake-manifest.json`
and the hash of `Lean.githash`.

(We hash `Lean.githash` in case the toolchain changes even though `lean-toolchain` hasn't.
This happens with the `lean-pr-testing-NNNN` toolchains when Lean 4 PRs are updated.)
-/
def getRootHash : CacheM UInt64 := do
  let mathlibDepPath := (← read).mathlibDepPath
  let rootFiles : List FilePath := [
    mathlibDepPath / "lakefile.lean",
    mathlibDepPath / "lean-toolchain",
    mathlibDepPath / "lake-manifest.json"]
  let hashes ← rootFiles.mapM fun path =>
    hashFileContents <$> IO.FS.readFile path
  return hash (rootHashGeneration :: hash Lean.githash :: hashes)

/--
Computes the hash of a file, which mixes:
* The root hash
* The hash of its relative path (inside its package directory)
* The hash of its content
* The hashes of the imported files that are part of `Mathlib`
-/
partial def getHash (filePath : FilePath) (visited : Std.HashSet FilePath := ∅) :
    HashM <| Option UInt64 := do
  if visited.contains filePath then
    throw <| IO.userError s!"dependency loop found involving {filePath}!"
  let visitedNew := visited.insert filePath
  match (← get).cache[filePath]? with
  | some hash? => return hash?
  | none =>
    let sp := (← read).srcSearchPath
    let fixedPath := (← IO.getSrcDir sp filePath) / filePath
    if !(← fixedPath.pathExists) then
      IO.println s!"Warning: {fixedPath} not found. Skipping all files that depend on it."
      if fixedPath.extension != "lean" then
        IO.println s!"Note that `lake exe cache get ...` expects file names \
          (e.g. `Mathlib/Init.lean`), not module names (e.g. `Mathlib.Init`)."
      modify fun stt => { stt with cache := stt.cache.insert filePath none }
      return none
    let content ← IO.FS.readFile fixedPath
    let fileImports' ← getFileImports content filePath.toString
    -- TODO: This line should eventually be removed: most code of cache still works
    -- with keys of the form `Mathlib/Init.lean`, `Aesop/Build.lean` instead of module
    -- names: `Mathlib.Init`, `Aesop.Build`, but `getFileImports` has been changed
    -- to return the latter, in preparation for the switch
    let fileImports := fileImports'.map fun (key, _) =>
      mkFilePath (key.components.map toString) |>.withExtension "lean"
    let mut importHashes := #[]
    for importHash? in ← fileImports.mapM (getHash (visited := visitedNew)) do
      match importHash? with
      | some importHash => importHashes := importHashes.push importHash
      | none =>
        modify fun stt => { stt with cache := stt.cache.insert filePath none }
        return none
    let rootHash := (← get).rootHash
    let pathHash := hash filePath.components
    let fileHash := hash <| rootHash :: pathHash :: hashFileContents content :: importHashes.toList
    modifyGet fun stt =>
      (some fileHash, { stt with
        hashMap := stt.hashMap.insert filePath fileHash
        cache   := stt.cache.insert   filePath (some fileHash)
        depsMap := stt.depsMap.insert filePath fileImports })

/-- Files to start hashing from. -/
def roots : Array FilePath := #["Mathlib.lean"]

/-- Main API to retrieve the hashes of the Lean files -/
def getHashMemo (extraRoots : Array FilePath) : CacheM HashMemo :=
  return (← StateT.run ((roots ++ extraRoots).mapM getHash) { rootHash := ← getRootHash }).2

end Cache.Hashing
