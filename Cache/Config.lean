import Lean.Data.RBMap
import Lean.Data.Json

open System (FilePath mkFilePath)
open Lean (Json RBMap)

namespace Cache

abbrev PkgDirs := Lean.RBMap String FilePath compare

structure Config where
  url : String
  head : FilePath
  rootRef : FilePath
  tokenEnvVar : String
  pkgDirs: PkgDirs

namespace Config

def FILE : FilePath :=
  ⟨"cache-config.json"⟩

@[inline] def Config.getBuildDir (cfg : Config) (k : String) : Option FilePath :=
  cfg.pkgDirs.find? k

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
    let some $ .str tokenEnvVar := x.find compare "tokenEnvVar"
      | return .error s!"{FILE} is missing the \"tokenEnvVar\" (string) field"
    let some $ .obj pkgDirs := x.find compare "pkgDirs"
      | return .error s!"{FILE} is missing the \"pkgDirs\" (object) field"
    let mut pkgDirs' := default
    for pair in pkgDirs.toArray do
      let .str path := pair.2 | return .error s!"Error when reading the build path for {pair.1}"
      pkgDirs' := pkgDirs'.insert pair.1 (mkFilePath $ path.splitOn "/")
    return .ok ⟨url, ⟨head⟩, mkFilePath $ rootRef.splitOn "/", tokenEnvVar, pkgDirs'⟩
  | _ => return .error s!"Invalid formatting for {FILE}"

end Cache.Config
