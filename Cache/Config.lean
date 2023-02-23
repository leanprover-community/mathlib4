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
  builds: RBMap String FilePath compare

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
    let some $ .obj builds := x.find compare "builds"
      | return .error s!"{FILE} is missing the \"builds\" (object) field"
    let mut builds' := default
    for pair in builds.toArray do
      let .str path := pair.2 | return .error s!"Error when reading the build path for {pair.1}"
      builds' := builds'.insert pair.1 (mkFilePath $ path.splitOn "/")
    return .ok ⟨url, ⟨head⟩, builds'⟩
  | _ => return .error s!"Invalid formatting for {FILE}"

end Cache.Config
