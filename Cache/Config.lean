import Lean.Data.RBMap
import Lean.Data.Json

open System (FilePath mkFilePath)
open Lean (Json RBMap)

namespace Cache

abbrev PkgDirs := Lean.RBMap String FilePath compare

structure Config where
  url : String
  head : FilePath
  rootDir : FilePath
  tokenEnvVar : String
  pkgDirs: PkgDirs

namespace Config

@[inline] def getBuildDir (cfg : Config) (k : String) : Option FilePath :=
  cfg.pkgDirs.find? k

def FILE : FilePath :=
  ⟨"cache-config.json"⟩

def stdTemplate : String :=
"{
  \"url\":\"https://lakecache.blob.core.windows.net/std4\",
  \"head\":\"Std.lean\",
  \"rootDir\":\"lake-packages/std\",
  \"tokenEnvVar\":\"STD_CACHE_SAS\",
  \"pkgDirs\":
  {
    \"Std\":\"lake-packages/std\"
  }
}\n"

def mathlibTemplate : String :=
"{
  \"url\":\"https://lakecache.blob.core.windows.net/mathlib4\",
  \"head\":\"Mathlib.lean\",
  \"rootDir\":\"lake-packages/mathlib\",
  \"tokenEnvVar\":\"MATHLIB_CACHE_SAS\",
  \"pkgDirs\":
  {
    \"Mathlib\":\"lake-packages/mathlib\",
    \"Aesop\":\"lake-packages/aesop\",
    \"Qq\":\"lake-packages/Qq\",
    \"Std\":\"lake-packages/std\"
  }
}\n"

def check : IO Bool := do
  if ← FILE.pathExists then return true else
  IO.println s!"Which cache config template to use?\n(0) Std\n(1) Mathlib"
  match (← (← IO.getStdin).getLine).trim with
  | "0" => IO.FS.writeFile FILE stdTemplate; return true
  | "1" => IO.FS.writeFile FILE mathlibTemplate; return true
  | _ => IO.println "Invalid template"; return false

def load : IO $ Except String Config := do
  let json ← match Json.parse (← IO.FS.readFile FILE) with
    | .ok json => pure json
    | .error e => return .error s!"Error when parsing {FILE}: {e}"
  match json with
  | .obj x =>
    let some $ .str url := x.find compare "url"
      | return .error s!"{FILE} is missing the \"url\" (string) field"
    let some $ .str head := x.find compare "head"
      | return .error s!"{FILE} is missing the \"head\" (string) field"
    let some $ .str rootDir := x.find compare "rootDir"
      | return .error s!"{FILE} is missing the \"rootDir\" (string) field"
    let some $ .str tokenEnvVar := x.find compare "tokenEnvVar"
      | return .error s!"{FILE} is missing the \"tokenEnvVar\" (string) field"
    let some $ .obj pkgDirs := x.find compare "pkgDirs"
      | return .error s!"{FILE} is missing the \"pkgDirs\" (object) field"
    let mut pkgDirs' := default
    for pair in pkgDirs.toArray do
      let .str path := pair.2 | return .error s!"Error when reading the build path for {pair.1}"
      pkgDirs' := pkgDirs'.insert pair.1 (mkFilePath $ path.splitOn "/")
    return .ok ⟨url, ⟨head⟩, mkFilePath $ rootDir.splitOn "/", tokenEnvVar, pkgDirs'⟩
  | _ => return .error s!"Invalid formatting for {FILE}"

end Cache.Config
