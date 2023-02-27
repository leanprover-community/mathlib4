/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean.Data.RBMap
import Lean.Data.Json

open System (FilePath mkFilePath)
open Lean (Json FromJson RBMap)

namespace Cache

abbrev PkgDirs := Lean.RBMap String FilePath compare

structure Config where
  url : String
  head : FilePath
  rootDir : FilePath
  tokenEnvVar : String
  pkgDirs: PkgDirs
  deriving FromJson

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
  match Json.parse (← IO.FS.readFile FILE) with
  | .ok json => pure $ Lean.fromJson? json
  | .error e => return .error s!"Error when parsing {FILE}: {e}"

end Cache.Config
