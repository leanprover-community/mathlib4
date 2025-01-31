/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster
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
* the path to the `.lean` file
* the file's hash (in `hashMap` and `cache`)

additionally, it contains the `rootHash` which reflects changes to Mathlib's
Lake project settings.
-/
structure HashMemo where
  /-- Hash of mathlib's lake project settings. -/
  rootHash : UInt64
  /-- Stores the imports of a module -/
  depsMap  : Std.HashMap Name (Array Name) := ∅
  /-- Stores the location of the source file of a module -/
  pathMap  : Std.HashMap Name FilePath := ∅
  /--
  For modules in Mathlib or upstream, this contains the same information
  as `hashMap`. Downstream modules have `none` here and do not appear in `hashMap`.
  -/
  cache    : Std.HashMap Name (Option UInt64) := ∅
  /-- Stores the hash of the module's content for modules in Mathlib or upstream. -/
  hashMap  : NameHashMap := ∅
  deriving Inhabited

partial def insertDeps (hashMap : NameHashMap) (mod : Name) (hashMemo : HashMemo) : NameHashMap :=
  if hashMap.contains mod then hashMap else
  match (hashMemo.depsMap[mod]?, hashMemo.hashMap[mod]?) with
  | (some deps, some hash) => deps.foldl (insertDeps · · hashMemo) (hashMap.insert mod hash)
  | _ => hashMap

/--
Filters the `HashMap` of a `HashMemo` so that it only contains key/value pairs such that every key:
* Belongs to the given list of module names or
* Corresponds to a module that's imported (transitively or not) by
  some module in the list module names
-/
def HashMemo.filterByNames (hashMemo : HashMemo) (mods : List Name) : IO NameHashMap := do
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
Read the imports from the raw file `content` and return an array of tuples
`(module name, source file)`.

Note: `mod` is the name of the parsed module and is only used for displaying an error
message if the parsing fails.
-/
def getFileImports (content : String) (mod : Name := default) :
    CacheM <| Array (Name × FilePath) := do
  let sp := (← read).searchPath
  let fileImports : Array Import ← Lean.parseImports' content mod.toString
  let out ← fileImports
    -- Lean core files can never be modified and therefore we do not need to process these
    -- moreover, it seems that `Lean.findLean` fails on these.
    |>.filter (! isInLeanCore ·.module)
    |>.mapM fun imp => do
      let impSourceFile ← Lean.findLean sp imp.module
      pure (imp.module, impSourceFile)
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
partial def getHash (mod : Name) (sourceFile : FilePath) (visited : Std.HashSet Name := ∅) :
    HashM <| Option UInt64 := do
  if visited.contains mod then
    throw <| IO.userError s!"dependency loop found involving {mod}!"
  match (← get).cache[mod]? with
  | some hash? => return hash?
  | none =>
    if !(← sourceFile.pathExists) then
      IO.println s!"Warning: {sourceFile} not found. Skipping all files that depend on it."
      modify fun stt => { stt with cache := stt.cache.insert mod none }
      return none
    let content ← IO.FS.readFile sourceFile
    let fileImports ← getFileImports content mod
    let mut importHashes := #[]
    for importHash? in ← fileImports.mapM (fun imp => getHash imp.1 imp.2 (visited.insert mod)) do
      match importHash? with
      | some importHash => importHashes := importHashes.push importHash
      | none =>
        -- one import did not have a hash --> invalidate hash of this module
        modify fun stt => { stt with cache := stt.cache.insert mod none }
        return none
    let rootHash := (← get).rootHash
    -- TODO: One might hash the modules name instead of this `c`,
    -- which exists in order to not change any generated hashes compared to previous versions.
    -- Changing this means the entire cache gets invalidated once and has to be rebuilt once.
    let c := (mod.components.dropLast.map toString).append [sourceFile.components.getLast!]
    let modHash := hash c -- TODO: change to `hash mod`
    let fileHash := hash <| rootHash :: modHash :: hashFileContents content :: importHashes.toList
    if isPartOfMathlibCache mod then
      -- mathlib/upstream: add hash to `hashMap`
      modifyGet fun stt =>
        (some fileHash, { stt with
          depsMap := stt.depsMap.insert mod (fileImports.map (·.1))
          pathMap := stt.pathMap.insert mod sourceFile
          cache   := stt.cache.insert   mod (some fileHash)
          hashMap := stt.hashMap.insert mod fileHash })
    else
      -- downstream: add `none` to `cache` and do not add hash to `hashMap`
      modifyGet fun stt =>
        (none, { stt with
          depsMap := stt.depsMap.insert mod (fileImports.map (·.1))
          pathMap := stt.pathMap.insert mod sourceFile
          cache   := stt.cache.insert   mod none
          hashMap := stt.hashMap })

/-- Main API to retrieve the hashes of the Lean files -/
def getHashMemo (extraRoots : Std.HashMap Name FilePath) : CacheM HashMemo := do
  -- TODO: `Std.HashMap.mapM` seems not to exist yet, so we got via `.toArray`.
  return (← StateT.run (extraRoots.toArray.mapM fun ⟨key, val⟩ => getHash key val)
    {rootHash := ← getRootHash}).2

end Cache.Hashing
