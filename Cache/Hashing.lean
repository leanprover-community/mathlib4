/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.IO
import Lean.Elab.ParseImportsFast

namespace Cache.Hashing

open System IO

structure HashMemo where
  depsMap : Lean.HashMap FilePath (Array FilePath)
  hashMap : HashMap
  deriving Inhabited

partial def insertDeps (hashMap : HashMap) (path : FilePath) (hashMemo : HashMemo) : HashMap :=
  if hashMap.contains path then hashMap else
  match (hashMemo.depsMap.find? path, hashMemo.hashMap.find? path) with
  | (some deps, some hash) => deps.foldl (insertDeps · · hashMemo) (hashMap.insert path hash)
  | _ => hashMap

/--
Filters the `HashMap` of a `HashMemo` so that it only contains key/value pairs such that every key:
* Belongs to the given list of file paths or
* Corresponds to a file that's imported (transitively of not) by some file in the list of file paths
-/
def HashMemo.filterByFilePaths (hashMemo : HashMemo) (filePaths : List FilePath) : IO HashMap := do
  let mut hashMap := default
  for filePath in filePaths do
    if hashMemo.hashMap.contains filePath then
      hashMap := insertDeps hashMap filePath hashMemo
    else throw $ IO.userError s!"No match for {filePath}"
  return hashMap

/-- We cache the hash of each file and their dependencies for later lookup -/
abbrev HashM := StateT HashMemo IO

/-- Gets the file paths to Mathlib files imported on a Lean source -/
def getFileImports (source : String) (pkgDirs : PackageDirs) : Array FilePath :=
  let s := Lean.ParseImports.main source (Lean.ParseImports.whitespace source {})
  let imps := s.imports.map (·.module.toString)
    |>.map (·.splitOn ".")
    |>.filter fun parts => match parts.head? with
      | some head => pkgDirs.contains head
      | none => false
  imps.map (mkFilePath · |>.withExtension "lean")

/--
Computes the root hash, which mixes the hashes of the content of:
* `lakefile.lean`
* `lean-toolchain`
* `lake-manifest.json`
-/
def getRootHash : IO UInt64 := do
  let rootFiles : List FilePath := ["lakefile.lean", "lean-toolchain", "lake-manifest.json"]
  let isMathlibRoot ← isMathlibRoot
  return hash $ ← rootFiles.mapM fun path => do
    pure $ ← IO.FS.readFile $ if isMathlibRoot then path else mathlibDepPath / path

initialize rootHash : UInt64 ← getRootHash

/--
Computes the hash of a file, which mixes:
* The root hash
* The hash of its relative path (inside its package directory)
* The hash of its content
* The hashes of the imported files that are part of `Mathlib`
-/
partial def getFileHash (filePath : FilePath) : HashM UInt64 := do
  match (← get).hashMap.find? filePath with
  | some hash => pure hash
  | none =>
    let content ← IO.FS.readFile $ (← IO.getPackageDir filePath) / filePath
    let fileImports := getFileImports content pkgDirs
    let importHashes ← fileImports.mapM getFileHash
    let pathHash := hash filePath.components
    let fileHash := hash $ rootHash :: pathHash :: content.hash :: importHashes.toList
    modifyGet fun stt =>
      (fileHash, { stt with
        hashMap := stt.hashMap.insert filePath fileHash
        depsMap := stt.depsMap.insert filePath fileImports })

/-- Main API to retrieve the hashes of the Lean files -/
def getHashMemo : IO HashMemo :=
  return (← StateT.run (getFileHash ⟨"Mathlib.lean"⟩) default).2

end Cache.Hashing
