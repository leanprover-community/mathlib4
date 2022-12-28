import Cache.IO

namespace Cache.Hashing

open System IO

/-- We store the root hash as a reader and cache the hash of each file for faster lookup -/
abbrev HashM := ReaderT UInt64 $ StateT IO.HashMap IO

/-- Gets the file paths to Mathlib files imported on a Lean source -/
def getFileImports (source : String) : Array FilePath :=
  let s := Lean.ParseImports.main source (Lean.ParseImports.whitespace source {})
  let imps := s.imports.map (·.module.toString)
    |>.map (·.splitOn ".")
    |>.filter fun parts => match parts.head? with
      | some head => IO.packageMap.contains head
      | none => false
  imps.map (mkFilePath · |>.withExtension "lean")

/--
Computes the root hash, which mixes the hashes of the content of:
* `lakefile.lean`
* `lean-toolchain`
* `lake-manifest.json`
-/
def getRootHash : IO UInt64 :=
  return hash [
    ← IO.FS.readFile ⟨"lakefile.lean"⟩,
    ← IO.FS.readFile ⟨"lean-toolchain"⟩,
    ← IO.FS.readFile ⟨"lake-manifest.json"⟩
  ]

/--
Computes the hash of a file, which mixes:
* The root hash
* The hash of its content
* The hashes of the imported files that are part of `Mathlib`
-/
partial def getFileHash (filePath : FilePath) : HashM UInt64 := do
  match (← get).find? filePath with
  | some hash => pure hash
  | none =>
    let content ← IO.FS.readFile $ (← IO.getPackageDir filePath) / filePath
    let importHashes ← (getFileImports content).mapM getFileHash
    let fileHash := hash $ (← read) :: content.hash :: importHashes.toList
    modifyGet (fileHash, ·.insert filePath fileHash)

/-- Main API to retrieve the hashes of the Lean files -/
def getHashes : IO IO.HashMap :=
  return (← StateT.run (ReaderT.run (getFileHash ⟨"Mathlib.lean"⟩) $ ← getRootHash) default).2

end Cache.Hashing
