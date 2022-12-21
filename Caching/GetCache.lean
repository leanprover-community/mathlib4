import Caching.Utils

def main : IO Unit := do
  let hashes ← getHashes
  hashes.forM fun filePath fileHash =>
    IO.println s!"{filePath} → {fileHash}"
