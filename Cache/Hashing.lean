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
  given as an argument), it visits all imports outside Lean core. Such a module has no hash.
  Its imports lead `cache` to the cache modules that it imports through other downstream
  modules.
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
The entries of `hashMap` for `modules` and the modules that they import, transitively.

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
        IO.println s!"{mod} is not in the olean cache. `cache get` gets the olean cache for its \
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
With `skipUnknown`, `getFileImports` prints a warning and leaves out an import that no package
in the search path has. Without it, such an import gets the result of `findLeanSource`: an error
for an unknown package, or a path that does not exist.

`fileName` names the file in the messages: the parse error and the warning.
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
        IO.println s!"Warning: {fileName} imports {imp.module}, but no package in the search \
          path has it. `cache` skips this import."
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

`sourceFile` is the source file of `mod`, which the caller has already found.
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
  -- A downstream module can import a module that no package has.
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
Main API to retrieve the hashes of the Lean files. It visits `Mathlib`, the modules in
`extraRoots`, and their imports (see `HashMemo`).
-/
public def getHashMemo (extraRoots : Std.HashMap Name FilePath) : CacheM HashMemo := do
  let visitAll : HashM Unit := (extraRoots.insertMany (← roots)).forM fun mod sourceFile =>
    discard <| getHash mod sourceFile
  return (← visitAll.run { rootHash := ← getRootHash }).2

end Cache.Hashing
