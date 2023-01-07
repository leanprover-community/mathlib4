/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Cache.IO
import Lean.Elab.ParseImportsFast

namespace Cache.Hashing

open System IO

/-- We cache the hash of each file for faster lookup -/
abbrev HashM := StateT IO.HashMap IO

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
  match (← get).find? filePath with
  | some hash => pure hash
  | none =>
    let content ← IO.FS.readFile $ (← IO.getPackageDir filePath) / filePath
    let importHashes ← (getFileImports content pkgDirs).mapM getFileHash
    let pathHash := hash filePath.components
    let fileHash := hash $ rootHash :: pathHash :: content.hash :: importHashes.toList
    modifyGet (fileHash, ·.insert filePath fileHash)

/-- Main API to retrieve the hashes of the Lean files -/
def getHashes : IO IO.HashMap :=
  return (← StateT.run (getFileHash ⟨"Mathlib.lean"⟩) default).2

end Cache.Hashing
