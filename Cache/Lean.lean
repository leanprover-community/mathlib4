/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/

import Lean.Data.Name
import Lean.Util.Path
import Init.System.FilePath

set_option autoImplicit false

/-!
# Helper Functions

This file contains helper functions that could potentially be upstreamed to Lean
or modify basic types from Lean.

Some functions here are duplicates from the folder `Mathlib/Lean/`.
-/

/--  -/
def Nat.toHexDigits (n : Nat) : Nat → (res : String := "") → String
  | 0, s => s
  | len+1, s =>
    let b := UInt8.ofNat (n >>> (len * 8))
    Nat.toHexDigits n len <|
      s.push (Nat.digitChar (b >>> 4).toNat) |>.push (Nat.digitChar (b &&& 15).toNat)

def UInt64.asLTar (n : UInt64) : String :=
  s!"{Nat.toHexDigits n.toNat 8}.ltar"

namespace Lean

open System hiding SearchPath in
/-- TODO: This is copied (without modification) from  the Lean source. It should
be in v4.17.0-rc1, I think. -/
partial def findLean (sp : SearchPath) (mod : Name) : IO FilePath := do
  if let some fname ← sp.findWithExt "lean" mod then
    return fname
  else
    let pkg := FilePath.mk <| mod.getRoot.toString (escape := false)
    throw <| IO.userError s!"unknown module prefix '{pkg}'\n\n\
      No directory '{pkg}' or file '{pkg}.lean' in the search path entries:\n\
      {"\n".intercalate <| sp.map (·.toString)}"

-- copied from Mathlib
/-- Create a `Name` from a list of components. -/
def Name.fromComponents : List Name → Name := go .anonymous where
  go : Name → List Name → Name
  | n, []        => n
  | n, s :: rest => go (s.updatePrefix n) rest

end Lean

namespace System.FilePath

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| aux path.components parent.components
where
  aux : List String → List String → List String
    | z@(x :: xs), y :: ys => if x == y then aux xs ys else z
    | [], _ => []
    | x, [] => x

end System.FilePath
