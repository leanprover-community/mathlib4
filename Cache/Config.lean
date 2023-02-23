import Lean.Data.RBMap
import Lean.Data.Json

open System (FilePath mkFilePath)
open Lean (Json RBMap)

namespace Cache.Config

def FILE : FilePath :=
  ⟨"cache-config.json"⟩

structure Config where
  url : String
  head : FilePath
  rootRef : FilePath
  buildDirs: RBMap String FilePath compare

@[inline] def Config.getBuildDir (cfg : Config) (k : String) : Option FilePath :=
  cfg.buildDirs.find? k

def load : IO $ Except String Config := do
  if !(← FILE.pathExists) then return .error s!"{FILE} not found"
  let json ← match Json.parse (← IO.FS.readFile FILE) with
    | .ok json => pure json
    | .error e => return .error s!"Error when parsing {FILE}: {e}"
  match json with
  | .obj x =>
    let some $ .str url := x.find compare "url"
      | return .error s!"{FILE} is missing the \"url\" (string) field"
    let some $ .str head := x.find compare "head"
      | return .error s!"{FILE} is missing the \"head\" (string) field"
    let some $ .str rootRef := x.find compare "rootRef"
      | return .error s!"{FILE} is missing the \"rootRef\" (string) field"
    let some $ .obj buildDirs := x.find compare "buildDirs"
      | return .error s!"{FILE} is missing the \"buildDirs\" (object) field"
    let mut buildDirs' := default
    for pair in buildDirs.toArray do
      let .str path := pair.2 | return .error s!"Error when reading the build path for {pair.1}"
      buildDirs' := buildDirs'.insert pair.1 (mkFilePath $ path.splitOn "/")
    return .ok ⟨url, ⟨head⟩, mkFilePath $ rootRef.splitOn "/", buildDirs'⟩
  | _ => return .error s!"Invalid formatting for {FILE}"

end Cache.Config
