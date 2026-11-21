/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jon Eugster
-/
module

public import Cache.IO
import Lean.Elab.ParseImportsFast

namespace Cache.Hashing

open Lean Cache.IO
open System hiding SearchPath

/--
The import graph of the modules that `cache` visits, and the hashes of the modules in the
Mathlib cache. From a module in the Mathlib cache, `cache` visits the imports in the cache.
From a module outside the cache, such as a downstream module given as an argument, it visits
all imports outside Lean core.
-/
public structure HashMemo where
  /-- Hash of mathlib's lake project settings. -/
  rootHash : UInt64
  /-- Maps each visited module to the modules it imports and that `cache` visits. -/
  depsMap  : Std.HashMap Name (Array Name) := ∅
  /-- The hash of each visited module that has a hash (see `getHash`). -/
  hashMap  : ModuleHashMap := ∅
  deriving Inhabited

/-- The modules in `mods` and the visited modules that they import, transitively. -/
def HashMemo.closure (hashMemo : HashMemo) (mods : Array Name) : Std.HashSet Name := Id.run do
  let mut visited : Std.HashSet Name := ∅
  let mut toVisit := mods
  while let some mod := toVisit.back? do
    toVisit := toVisit.pop
    if visited.contains mod then continue
    visited := visited.insert mod
    toVisit := toVisit ++ hashMemo.depsMap.getD mod #[]
  return visited

/--
The entries of `hashMap` that `get` selects for the roots `modules`: the closure of each root in
the Mathlib cache, and the modules that the other roots import and that `Mathlib` also imports.
CI uploads the cache only for the closure of `Mathlib`.
-/
public def HashMemo.filterByRootModules (hashMemo : HashMemo) (modules : List Name) :
    ModuleHashMap :=
  let (cacheRoots, otherRoots) := modules.toArray.partition isPartOfMathlibCache
  -- A root without a hash, such as a downstream module, contributes only its imports.
  let cacheClosure := hashMemo.closure cacheRoots
  let otherClosure := hashMemo.closure otherRoots
  let mathlibClosure := if otherRoots.isEmpty then ∅ else hashMemo.closure #[`Mathlib]
  hashMemo.hashMap.filter fun mod _ =>
    cacheClosure.contains mod || (otherClosure.contains mod && mathlibClosure.contains mod)

/-- We cache the hash of each file and their dependencies for later lookup -/
abbrev HashM := StateT HashMemo CacheM

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
-/
def getRootHash : CacheM UInt64 := do
  let mathlibDepPath := (← read).mathlibDepPath
  let rootFiles : List FilePath := [
    mathlibDepPath / "lakefile.lean",
    mathlibDepPath / "lean-toolchain",
    mathlibDepPath / "lake-manifest.json"]
  let hashes ← rootFiles.mapM fun path =>
    hashFileContents <$> IO.FS.readFile path
  return hash (rootHashGeneration :: hashes)

/--
Visits `mod` and its imports (see `HashMemo`), and returns the hash of `mod`.
The hash of a module in the Mathlib cache mixes:
* The root hash
* The hash of its relative path (inside its package directory)
* The hash of its content
* The hashes of the imported files that are part of the Mathlib cache

Only a module in the Mathlib cache whose imports all have a hash gets a hash.
-/
partial def getHash (mod : Name) (sourceFile? : Option FilePath)
    (visiting : Std.HashSet Name := ∅) : HashM <| Option UInt64 := do
  if visiting.contains mod then
    throw <| IO.userError s!"dependency loop found involving {mod}!"
  let stt ← get
  if stt.depsMap.contains mod then return stt.hashMap[mod]?
  let inCache := isPartOfMathlibCache mod
  let some sourceFile ← sourceFile?.filterM (·.pathExists) | do
    let sourceFile :=
      sourceFile?.getD (mkFilePath (mod.components.map toString) |>.addExtension "lean")
    IO.println s!"Warning: {sourceFile} not found. Skipping all files that depend on it."
    modify fun stt => { stt with depsMap := stt.depsMap.insert mod #[] }
    return none
  let content ← IO.FS.readFile sourceFile
  let imports := (← Lean.parseImports' content mod.toString).imports.map (·.module)
    |>.filter fun imp => if inCache then isPartOfMathlibCache imp else !isInLeanCore imp
  let sp := (← read).srcSearchPath
  let importHashes ← imports.mapM fun imp => do
    getHash imp (← sp.findLeanSource? imp) (visiting.insert mod)
  modify fun stt => { stt with depsMap := stt.depsMap.insert mod imports }
  unless inCache do return none
  let some importHashes := importHashes.mapM id | return none
  /-
  TODO: Currently, the cache uses the hash of the unresolved file name
  (e.g. `Mathlib/Init.lean`) which is reconstructed from the module name
  (e.g. `Mathlib.Init`) in `path`. It could, however, directly use `hash mod` instead.

  We can change this at any time causing a one-time cache invalidation, just as
  a toolchain-bump would.
  -/
  let filePath := mkFilePath (mod.components.map toString) |>.withExtension "lean"
  let pathHash := hash filePath.components -- TODO: change to `hash mod`
  let fileHash :=
    hash <| (← get).rootHash :: pathHash :: hashFileContents content :: importHashes.toList
  modify fun stt => { stt with hashMap := stt.hashMap.insert mod fileHash }
  return some fileHash

/-- Files to start hashing from. -/
def roots : CacheM <| Array <| Name × FilePath := do
  let mathlibDepPath := (← read).mathlibDepPath
  return #[(`Mathlib, (mathlibDepPath / "Mathlib.lean"))]

/-- Main API to retrieve the hashes of the Lean files -/
public def getHashMemo (extraRoots : Std.HashMap Name FilePath) : CacheM HashMemo :=
  -- TODO: `Std.HashMap.mapM` seems not to exist yet, so we go via `.toArray`.
  return (← StateT.run ((extraRoots.insertMany (← roots)).toArray.mapM fun
    ⟨key, val⟩ => getHash key (some val)) { rootHash := ← getRootHash }).2

end Cache.Hashing
