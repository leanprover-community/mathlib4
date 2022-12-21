import Caching.Utils

open System

def curlPieceForPair (filePath : FilePath) (fileHash : UInt64) : String :=
  let builtFilePaths := builtFileKinds.map fun kind =>
    s!"{cachedBuiltFileURL fileHash kind} -o {builtFilePath filePath kind}"
  " ".intercalate $ builtFilePaths.map toString

def main : IO Unit := do
  let hashes ← getHashes
  let curlCMD := hashes.fold (init := "curl --parallel") fun acc filePath fileHash =>
    s!"{acc} {curlPieceForPair filePath fileHash}"
  IO.println curlCMD
