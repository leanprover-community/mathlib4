import Lean.Data.HashMap

open System

def LIBDIR : FilePath :=
  "build" / "lib"

def URL : String := "https://foo"

partial def getLeanFilePaths (fp : FilePath) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    let mut extra : Array FilePath := #[]
    for dirEntry in ← fp.readDir do
      for innerFp in ← getLeanFilePaths dirEntry.path do
        extra := extra.push innerFp
    return acc.append extra
  else match fp.extension with
    | some "lean" => return acc.push fp
    | _ => return acc

/-- Extracts the relevant imports of a Lean source code -/
def getFileImports (content : String) : List FilePath :=
  let importLines := content.splitOn "\n" |>.filter (·.startsWith "import Mathlib.")
  let imports := importLines.map fun line =>
    let line := (line.splitOn "import ").get! 1
      |>.replace "." "/"
      |>.splitOn " "
      |>.head!
    line ++ ".lean"
  imports.map FilePath.mk

def getRootHash : IO UInt64 :=
  return hash [
    ← IO.FS.readFile ⟨"lakefile.lean"⟩,
    ← IO.FS.readFile ⟨"lean-toolchain"⟩,
    ← IO.FS.readFile ⟨"lake-manifest.json"⟩
  ]

/-- We store the root hash as a reader and cache the hash of each file for faster lookup -/
abbrev HashM := ReaderT UInt64 $ StateT (Lean.HashMap FilePath UInt64) IO

partial def getFileHash (filePath : FilePath) : HashM UInt64 := do
  match (← get).find? filePath with
  | some hash => pure hash
  | none =>
    let content ← IO.FS.readFile filePath
    let importHashes ← (getFileImports content).mapM getFileHash
    let fileHash := hash $ (← read) :: content.hash :: importHashes
    modifyGet (fileHash, ·.insert filePath fileHash)

def cacheHashes : HashM Unit := do
  let leanFilePaths ← getLeanFilePaths ⟨"Mathlib"⟩
  leanFilePaths.forM (discard $ getFileHash ·)

def getHashes : IO $ Lean.HashMap FilePath UInt64 :=
  return (← StateT.run (ReaderT.run cacheHashes (← getRootHash)) default).2

inductive BuiltFileKind
  | olean | ilean | trace

def BuiltFileKind.extension : BuiltFileKind → String
  | .olean => "olean"
  | .ilean => "ilean"
  | .trace => "trace"

def builtFilePath (leanFilePath : FilePath) (kind : BuiltFileKind) : FilePath :=
  LIBDIR / leanFilePath.withExtension kind.extension

def builtFileKinds : List BuiltFileKind :=
  [.olean, .ilean, .trace]

def cachedBuiltFileURL (hash : UInt64) (kind : BuiltFileKind) : String :=
  s!"{URL}/{hash}.{kind.extension}"
