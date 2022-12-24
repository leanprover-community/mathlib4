import Cache.IOUtils

namespace Cache

open System IO FS

/-- We store the root hash as a reader and cache the hash of each file for faster lookup -/
abbrev HashM := ReaderT UInt64 $ StateT (Lean.HashMap FilePath UInt64) IO

partial def getFileHash (filePath : FilePath) : HashM UInt64 := do
  match (← get).find? filePath with
  | some hash => pure hash
  | none =>
    let content ← readFile filePath
    let importHashes ← (← getFilesWithExtension content "lean").mapM getFileHash
    let fileHash := hash $ (← read) :: content.hash :: importHashes.toList
    modifyGet (fileHash, ·.insert filePath fileHash)

def cacheHashes : HashM Unit := do
  let leanFilePaths ← getFilesWithExtension ⟨"Mathlib"⟩ "lean"
  leanFilePaths.forM (discard $ getFileHash ·)

def getRootHash : IO UInt64 :=
  return hash [
    ← readFile ⟨"lakefile.lean"⟩,
    ← readFile ⟨"lean-toolchain"⟩,
    ← readFile ⟨"lake-manifest.json"⟩
  ]

def getHashes : IO $ Lean.HashMap FilePath UInt64 :=
  return (← StateT.run (ReaderT.run cacheHashes (← getRootHash)) default).2

end Cache
