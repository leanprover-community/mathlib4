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
The `HashMemo` contains all information `Cache` needs about the modules:
* the name
* its imports
* the file's hash (in `hashMap` and `cache`)

additionally, it contains the `rootHash` which reflects changes to Mathlib's
Lake project settings.
-/
public structure HashMemo where
  /-- Hash of mathlib's lake project settings. -/
  rootHash : UInt64
  /--
  Maps a module to the modules it imports.
  For a module in the Mathlib cache, these are its imports in the Mathlib cache.
  For a module outside the Mathlib cache, these are its imports outside Lean core
  (see `addOutsideCache`).
  -/
  depsMap  : Std.HashMap Name (Array Name) := ∅
  /--
  For files with a valid hash (usually Mathlib and upstream),
  this contains the same information as `hashMap`.
  Other files have `none` here and do not appear in `hashMap`
  (e.g. `.lean` source could not be found, imports a file without valid hash).
  -/
  cache    : Std.HashMap Name (Option UInt64) := ∅
  /-- Stores the hash of the module's content for modules in Mathlib or upstream. -/
  hashMap  : ModuleHashMap := ∅
  deriving Inhabited

/--
Adds `mod` and the modules it imports, transitively, to the hash map in the state.
The state also holds the set of visited modules.

A module without a hash does not go into the hash map. If `depsMap` has its imports
(a module outside the Mathlib cache), the traversal continues through them.
-/
partial def insertDeps (hashMemo : HashMemo) (mod : Name) :
    StateM (ModuleHashMap × Std.HashSet Name) Unit := do
  if (← get).2.contains mod then return
  modify fun (hashMap, visited) => (hashMap, visited.insert mod)
  let some deps := hashMemo.depsMap[mod]? | return
  if let some hash := hashMemo.hashMap[mod]? then
    modify fun (hashMap, visited) => (hashMap.insert mod hash, visited)
  for dep in deps do
    insertDeps hashMemo dep

/--
Filters the `hashMap` of a `HashMemo` so that it only contains key/value pairs such that every key:
* Belongs to the given list of module names or
* Corresponds to a module that's imported (transitively or not) by
  some module in the list module names

A module outside the Mathlib cache has no hash. For such a module, the result contains the
modules in the Mathlib cache that it imports, also through other modules outside the cache.
-/
public def HashMemo.filterByRootModules (hashMemo : HashMemo) (modules : List Name) :
    IO ModuleHashMap := do
  let mut state := (∅, ∅)
  for mod in modules do
    if !hashMemo.hashMap.contains mod then
      if hashMemo.depsMap.contains mod then
        IO.println s!"{mod} is not covered by the olean cache. \
          Getting the olean cache for its imports."
      else
        IO.println s!"{mod} is not covered by the olean cache."
    state := (insertDeps hashMemo mod).run state |>.2
  return state.1

/-- We cache the hash of each file and their dependencies for later lookup -/
abbrev HashM := StateT HashMemo CacheM

/--
Read the imports from the raw file `content` and return an array of tuples
`(module name, source file)`, one per import.

The result contains only the imports for which `keep` is `true`.

Note: `fileName` is a string which is purely used for displaying an error message if
parsing imports from `content` should fail. It is intended to be the file's name.
-/
def getFileImports (content : String) (fileName : String := "")
    (keep : Name → Bool := isPartOfMathlibCache) :
    CacheM <| Array (Name × FilePath) := do
  let sp := (← read).srcSearchPath
  let res ← Lean.parseImports' content fileName
  res.imports
    |>.filter (keep ·.module)
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
Computes the hash of a file, which mixes:
* The root hash
* The hash of its relative path (inside its package directory)
* The hash of its content
* The hashes of the imported files that are part of `Mathlib`

Note: we pass `sourceFile` along to avoid searching for it twice
-/
partial def getHash (mod : Name) (sourceFile : FilePath) (visited : Std.HashSet Name := ∅) :
    HashM <| Option UInt64 := do
  if visited.contains mod then
    throw <| IO.userError s!"dependency loop found involving {mod}!"
  let visitedₙ := visited.insert mod
  match (← get).cache[mod]? with
  | some hash? => return hash?
  | none =>
    if !(← sourceFile.pathExists) then
      IO.println s!"Warning: {sourceFile} not found. Skipping all files that depend on it."
      modify fun stt => { stt with cache := stt.cache.insert mod none }
      return none
    let content ← IO.FS.readFile sourceFile
    let fileImports ← getFileImports content mod.toString
    let mut importHashes := #[]
    for importHash? in
        ← fileImports.mapM (fun (modₙ, sourceFileₙ) => getHash modₙ sourceFileₙ visitedₙ) do
      match importHash? with
      | some importHash => importHashes := importHashes.push importHash
      | none =>
        -- one import did not have a hash: invalidate hash of this module
        modify fun stt => { stt with cache := stt.cache.insert mod none }
        return none
    /-
    TODO: Currently, the cache uses the hash of the unresolved file name
    (e.g. `Mathlib/Init.lean`) which is reconstructed from the module name
    (e.g. `Mathlib.Init`) in `path`. It could, however, directly use `hash mod` instead.

    We can change this at any time causing a one-time cache invalidation, just as
    a toolchain-bump would.
    -/
    let filePath := mkFilePath (mod.components.map toString) |>.withExtension "lean"

    let rootHash := (← get).rootHash
    let pathHash := hash filePath.components -- TODO: change to `hash mod`
    let fileHash := hash <| rootHash :: pathHash :: hashFileContents content :: importHashes.toList
    modifyGet fun stt =>
      (some fileHash, { stt with
        hashMap := stt.hashMap.insert mod fileHash
        cache   := stt.cache.insert   mod (some fileHash)
        depsMap := stt.depsMap.insert mod (fileImports.map (·.1)) })

/--
Records the imports of `mod`, a module outside the Mathlib cache, in `depsMap`, and hashes
the modules in the Mathlib cache that it imports.

The cache has no files for `mod`, so `mod` gets no hash. Imports outside the Mathlib cache
get the same treatment, so that a downstream module reaches the Mathlib cache modules it
imports through other downstream modules. Imports from Lean core are not followed.
-/
partial def addOutsideCache (mod : Name) (sourceFile : FilePath) : HashM Unit := do
  if (← get).depsMap.contains mod then return
  if !(← sourceFile.pathExists) then
    IO.println s!"Warning: {sourceFile} not found. Skipping it and its imports."
    return
  let content ← IO.FS.readFile sourceFile
  let fileImports ← getFileImports content mod.toString (keep := (!isInLeanCore ·))
  modify fun stt => { stt with depsMap := stt.depsMap.insert mod (fileImports.map (·.1)) }
  for (modₙ, sourceFileₙ) in fileImports do
    if isPartOfMathlibCache modₙ then
      discard <| getHash modₙ sourceFileₙ
    else
      addOutsideCache modₙ sourceFileₙ

/-- Files to start hashing from. -/
def roots : CacheM <| Array <| Name × FilePath := do
  let mathlibDepPath := (← read).mathlibDepPath
  return #[(`Mathlib, (mathlibDepPath / "Mathlib.lean"))]

/--
Main API to retrieve the hashes of the Lean files.

The hashes always cover `Mathlib` and its imports. A module in `extraRoots` that is outside
the Mathlib cache gets no hash; `addOutsideCache` follows its imports instead.
-/
public def getHashMemo (extraRoots : Std.HashMap Name FilePath) : CacheM HashMemo := do
  let roots := extraRoots.insertMany (← roots)
  let act : HashM Unit := roots.forM fun mod sourceFile =>
    if isPartOfMathlibCache mod then discard <| getHash mod sourceFile
    else addOutsideCache mod sourceFile
  return (← act.run { rootHash := ← getRootHash }).2

end Cache.Hashing
