/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Arthur Paulino
-/

import Lean.Data.Json
import Lean.Util.Path

/-!
# Helper Functions

This file contains helper functions that could potentially be upstreamed to Lean
or replaced by an appropriate function from Lean.

Some functions here are duplicates from the folder `Mathlib/Lean/`.
-/

/-- Format as hex digit string. Used by `Cache` to format hashes. -/
def Nat.toHexDigits (n : Nat) : Nat → (res : String := "") → String
  | 0, s => s
  | len + 1, s =>
    let b := UInt8.ofNat (n >>> (len * 8))
    Nat.toHexDigits n len <|
      s.push (Nat.digitChar (b >>> 4).toNat) |>.push (Nat.digitChar (b &&& 15).toNat)

/-- Format hash as hex digit with extension `.ltar` -/
def UInt64.asLTar (n : UInt64) : String :=
  s!"{Nat.toHexDigits n.toNat 8}.ltar"

-- copied from Mathlib
/-- Create a `Name` from a list of components. -/
def Lean.Name.fromComponents : List Name → Name := go .anonymous where
  go : Name → List Name → Name
  | n, []        => n
  | n, s :: rest => go (s.updatePrefix n) rest

namespace Lean.SearchPath

open System in

/--
Find the source directory for a module. This could be `.`
(or in fact also something uncleaned like `./././.`) if the
module is part of the current package, or something like `.lake/packages/mathlib` if the
module is from a dependency.

This is an exact copy of the first part of `Lean.SearchPath.findWithExt` which, in turn,
is used by `Lean.findLean sp mod`. In the future, `findWithExt` could be refactored to
expose this base path.
-/
def findWithExtBase (sp : SearchPath) (ext : String) (mod : Name) : IO (Option FilePath) := do
  let pkg := mod.getRoot.toString (escape := false)
  sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).addExtension ext).pathExists

end Lean.SearchPath

namespace System.FilePath

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| go path.components parent.components
where
  go : List String → List String → List String
  | path@(x :: xs), y :: ys => if x == y then go xs ys else path
  | [], _ => []
  | path, [] => path

end System.FilePath
