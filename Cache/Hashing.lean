import Cache.IOUtils

namespace Cache.Hashing

open System IO

/-- We store the root hash as a reader and cache the hash of each file for faster lookup -/
abbrev HashM := ReaderT UInt64 $ StateT (Std.HashMap FilePath UInt64) IO

partial def getFileHash (filePath : FilePath) : HashM UInt64 := do
  match (← get).find? filePath with
  | some hash => pure hash
  | none =>
    let content ← IO.FS.readFile filePath
    let importHashes ← (← getFilesWithExtension content "lean").mapM getFileHash
    let fileHash := hash $ (← read) :: content.hash :: importHashes.toList
    modifyGet (fileHash, ·.insert filePath fileHash)

def cacheHashes : HashM Unit := do
  let leanFilePaths ← getFilesWithExtension ⟨"Mathlib"⟩ "lean"
  leanFilePaths.forM (discard $ getFileHash ·)

def getRootHash : IO UInt64 :=
  return hash [
    ← IO.FS.readFile ⟨"lakefile.lean"⟩,
    ← IO.FS.readFile ⟨"lean-toolchain"⟩,
    ← IO.FS.readFile ⟨"lake-manifest.json"⟩
  ]

def getHashes : IO $ Std.HashMap FilePath UInt64 :=
  return (← StateT.run (ReaderT.run cacheHashes $ ← getRootHash) default).2

end Cache.Hashing
