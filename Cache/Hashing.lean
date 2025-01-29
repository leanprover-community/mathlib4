/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.IO
import Lean.Elab.ParseImportsFast
import Lake.Build.Trace

namespace Cache.Hashing

open Lean IO
open System hiding SearchPath

structure HashMemo where
  /-- hashes `lakefile`, `lean-toolchain` and `lake-manifest`. -/
  rootHash : UInt64
  /-- Array of imports for each module -/
  depsMap  : Std.HashMap Name (Array Name) := {}
  cache    : Std.HashMap Name (Option UInt64) := {}
  /-- The location of each module's source file -/
  pathMap  : Std.HashMap Name FilePath := {}
  /-- The hashes of each module's content -/
  hashMap  : HashMap := {}
  deriving Inhabited

partial def insertDeps (hashMap : HashMap) (mod : Name) (hashMemo : HashMemo) : HashMap :=
  if hashMap.contains mod then hashMap else
  match (hashMemo.depsMap[mod]?, hashMemo.hashMap[mod]?) with
  | (some deps, some hash) => deps.foldl (insertDeps · · hashMemo) (hashMap.insert mod hash)
  | _ => hashMap

/--
Filters the `HashMap` of a `HashMemo` so that it only contains key/value pairs such that every key:
* Belongs to the given list of module names or
* Corresponds to a module that's imported (transitively of not) by
  some module in the list module names
-/
def HashMemo.filterByNames (hashMemo : HashMemo) (mods : List Name) : IO HashMap := do
  let mut hashMap := ∅
  for mod in mods do
    if hashMemo.hashMap.contains mod then
      hashMap := insertDeps hashMap mod hashMemo
    else
      IO.println s!"{mod} is not covered by the olean cache."
  return hashMap

/-- We cache the hash of each file and their dependencies for later lookup -/
abbrev HashM := StateT HashMemo CacheM

/--
Read the imports from the raw file `content` and returns an array of tuples
`(module name, source file)`.

Note: `mod` is the name of the parsed module and is only used for displaying an error
message if the parsing fails.
-/
def getFileImports (content : String) (mod : Name := default) :
    CacheM <| Array (Name × FilePath) := do
  let sp := (← read).searchPath
  -- TODO: What happens with these?
  let excluded : Array Name := #[`Init, `Lean, `Std, `Lake]
  let fileImports ← Lean.parseImports' content mod.toString
  let out ← fileImports.filter (fun imp => !excluded.any (·.isPrefixOf imp.module)) |>.mapM (fun imp => do
    let impSourceFile ← Lean.findLean sp imp.module
    pure (imp.module, impSourceFile))
  pure out

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
  return hash (hash Lean.githash :: hashes)

/--
Computes the hash of a file, which mixes:
* The root hash
* The hash of its relative path (inside its package directory)
* The hash of its content
* The hashes of the imported files that are part of `Mathlib`
-/
partial def getHash (mod : Name) (sourceFile : FilePath) : HashM <| Option UInt64 := do
  match (← get).cache[mod]? with
  | some hash? => return hash?
  | none =>
    -- let fixedPath := (← IO.getPackageDir filePath) / filePath
    if !(← sourceFile.pathExists) then
      IO.println s!"Warning: {sourceFile} not found. Skipping all files that depend on it."
      -- if fixedPath.extension != "lean" then
      --   IO.println s!"Note that `lake exe cache get ...` expects file names \
      --     (e.g. `Mathlib/Init.lean`), not module names (e.g. `Mathlib.Init`)."
      modify fun stt => { stt with cache := stt.cache.insert mod none }
      return none
    let content ← IO.FS.readFile sourceFile
    let fileImports ← getFileImports content mod
    let mut importHashes := #[]
    for importHash? in ← fileImports.mapM (fun imp => getHash imp.1 imp.2) do
      match importHash? with
      | some importHash => importHashes := importHashes.push importHash
      | none =>
        -- one import did not have a hash --> invalidate hash of this module
        modify fun stt => { stt with cache := stt.cache.insert mod none }
        return none
    let rootHash := (← get).rootHash
    -- TODO: I want to hash the module name instead but that invalidates all existing cache
    -- so we stick with this `c` for now.
    let c := (mod.components.dropLast.map toString).append [sourceFile.components.getLast!]
    let pathHash := hash c -- hash mod
    let fileHash := hash <| rootHash :: pathHash :: hashFileContents content :: importHashes.toList
    modifyGet fun stt =>
      (some fileHash, { stt with
        hashMap := stt.hashMap.insert mod fileHash
        pathMap := stt.pathMap.insert mod sourceFile
        cache   := stt.cache.insert   mod (some fileHash)
        depsMap := stt.depsMap.insert mod (fileImports.map (·.1)) })

/-- Main API to retrieve the hashes of the Lean files -/
def getHashMemo (extraRoots : Std.HashMap Name FilePath) : CacheM HashMemo := do
  -- TODO: `Std.HashMap.mapM` seems not to exist yet.
  return (← StateT.run (extraRoots.toArray.mapM (fun ⟨key, val⟩ => getHash key val)) {
    rootHash := ← getRootHash}).2

end Cache.Hashing
