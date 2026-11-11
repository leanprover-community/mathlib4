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
Mathlib cache.

`cache` starts at the root modules and visits their imports, transitively:
* From a module in the Mathlib cache, it visits only the imports in the Mathlib cache.
  These are the imports that go into the module's hash.
* From a module outside the Mathlib cache (for example, a module of a downstream project
  given as an argument), it visits all imports outside Lean core. Such a module has no hash,
  but this lets `cache` find the cache modules it imports through other downstream modules.

Additionally, the `HashMemo` contains the `rootHash`, which reflects changes to Mathlib's
Lake project settings.
-/
public structure HashMemo where
  /-- Hash of mathlib's lake project settings. -/
  rootHash : UInt64
  /-- Maps each visited module to the modules it imports and that `cache` visits. -/
  depsMap  : Std.HashMap Name (Array Name) := ∅
  /--
  The hash of each visited module in the Mathlib cache whose source file exists and whose
  imports all have a hash. Other visited modules are not in `hashMap`.
  -/
  hashMap  : ModuleHashMap := ∅
  deriving Inhabited

/--
Filters the `hashMap` of a `HashMemo` so that it only contains key/value pairs such that every key:
* Belongs to the given list of module names or
* Corresponds to a module that's imported (transitively or not) by
  some module in the list module names

A module without a hash is not in the result, but its imports are. Thus, for a module outside
the Mathlib cache, the result contains the cache modules that it imports.
-/
public def HashMemo.filterByRootModules (hashMemo : HashMemo) (modules : List Name) :
    IO ModuleHashMap := do
  for mod in modules do
    unless hashMemo.hashMap.contains mod do
      if isPartOfMathlibCache mod then
        IO.println s!"{mod} is not covered by the olean cache."
      else
        IO.println s!"{mod} is not part of the olean cache: getting the olean cache for its \
          imports."
  let mut hashMap := ∅
  let mut visited : Std.HashSet Name := ∅
  let mut toVisit := modules.toArray
  while let some mod := toVisit.back? do
    toVisit := toVisit.pop
    if visited.contains mod then continue
    visited := visited.insert mod
    if let some hash := hashMemo.hashMap[mod]? then
      hashMap := hashMap.insert mod hash
    toVisit := toVisit ++ hashMemo.depsMap.getD mod #[]
  return hashMap

/-- We cache the hash of each file and their dependencies for later lookup -/
abbrev HashM := StateT HashMemo CacheM

/--
Whether `cache` visits the import `imp` of the module `mod`. See `HashMemo`.
-/
def visitsImport (mod imp : Name) : Bool :=
  if isPartOfMathlibCache mod then isPartOfMathlibCache imp else !isInLeanCore imp

/--
Read the imports from the raw file `content` and return an array of tuples
`(module name, source file)`, one per import for which `keep` is `true`.
With `skipUnknown`, an import that no package in the search path has is left out with a
warning. Otherwise, such an import is an error.

Note: `fileName` is a string which is purely used for displaying an error message if
parsing imports from `content` should fail. It is intended to be the file's name.
-/
def getFileImports (content : String) (keep : Name → Bool) (fileName : String := "")
    (skipUnknown := false) : CacheM <| Array (Name × FilePath) := do
  let sp := (← read).srcSearchPath
  let res ← Lean.parseImports' content fileName
  res.imports
    |>.filter (keep ·.module)
    |>.filterMapM fun imp => do
      if !skipUnknown then
        return some (imp.module, ← sp.findLeanSource imp.module)
      let some impSourceFile ← sp.findLeanSource? imp.module | do
        IO.println s!"Warning: no package in the search path has {imp.module}, \
          which {fileName} imports. Skipping it."
        return none
      return some (imp.module, impSourceFile)

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

A module outside the Mathlib cache has no hash. A module with an import without a hash
has no hash either.

Note: we pass `sourceFile` along to avoid searching for it twice
-/
partial def getHash (mod : Name) (sourceFile : FilePath) (visiting : Std.HashSet Name := ∅) :
    HashM <| Option UInt64 := do
  if visiting.contains mod then
    throw <| IO.userError s!"dependency loop found involving {mod}!"
  let stt ← get
  if stt.depsMap.contains mod then return stt.hashMap[mod]?
  if !(← sourceFile.pathExists) then
    IO.println s!"Warning: {sourceFile} not found. Skipping all files that depend on it."
    modify fun stt => { stt with depsMap := stt.depsMap.insert mod #[] }
    return none
  let content ← IO.FS.readFile sourceFile
  -- An unknown import of a downstream module is not an error: `cache` cannot get files for
  -- a module outside the Mathlib cache anyway.
  let fileImports ← getFileImports content (visitsImport mod) mod.toString
    (skipUnknown := !isPartOfMathlibCache mod)
  let importHashes ← fileImports.mapM fun (modₙ, sourceFileₙ) =>
    getHash modₙ sourceFileₙ (visiting.insert mod)
  modify fun stt => { stt with depsMap := stt.depsMap.insert mod (fileImports.map (·.1)) }
  if !isPartOfMathlibCache mod then return none
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
    hash <| stt.rootHash :: pathHash :: hashFileContents content :: importHashes.toList
  modify fun stt => { stt with hashMap := stt.hashMap.insert mod fileHash }
  return some fileHash

/-- Files to start hashing from. -/
def roots : CacheM <| Array <| Name × FilePath := do
  let mathlibDepPath := (← read).mathlibDepPath
  return #[(`Mathlib, (mathlibDepPath / "Mathlib.lean"))]

/--
Main API to retrieve the hashes of the Lean files.

`cache` visits `Mathlib` and the modules in `extraRoots`, and their imports (see `HashMemo`).
-/
public def getHashMemo (extraRoots : Std.HashMap Name FilePath) : CacheM HashMemo := do
  let visitAll : HashM Unit := (extraRoots.insertMany (← roots)).forM fun mod sourceFile =>
    discard <| getHash mod sourceFile
  return (← visitAll.run { rootHash := ← getRootHash }).2

end Cache.Hashing
