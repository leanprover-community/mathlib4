/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/

import Lean.Data.Name
import Lean.Util.Path
import Init.System.FilePath
import Std

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

/--
Returns true if `target` lives inside `path`.
Does not check if the two actually exist.

The paths can contain arbitrary amounts of ".", "" or "..".
However, if the paths do not contain the same amount of leading "..", it
will return `False` as the real system path is unknown to the function.

For example, `contains (".." / "myFolder") ("myFolder" / "..")` will always return `false`
even though it might be true depending on which local working directory on is in
(which `contains` doesn't know about since it's not in `IO`)
-/
def contains (path target : FilePath) : Bool :=
  go path.components target.components
where
  go : List String → List String → Bool
    -- ignore leading "." or ""
    | "." :: path, target => go path target
    | path, "." :: target => go path target
    | "" :: path, target => go path target
    | path, "" :: target => go path target
    -- must not start with unequal quantity of ".."
    | ".." :: path, ".." :: target => go path target
    | ".." :: _, _ => false
    | _, ".." :: _ => false
    -- cancel entry with following ".."
    | _ :: ".." :: path, target => go path target
    | path, _ :: ".." :: target => go path target
    -- base cases
    | [], _ => true
    | _ :: _, [] => false
    -- recursion
    | p :: ath, t :: arget => if p == t then go ath arget else false

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| aux path.components parent.components
where
  aux : List String → List String → List String
    | z@(x :: xs), y :: ys => if x == y then aux xs ys else z
    | [], _ => []
    | x, [] => x

end System.FilePath
