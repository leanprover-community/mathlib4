/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/

import Lean.Data.Name
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
  | len+1, s =>
    let b := UInt8.ofNat (n >>> (len * 8))
    Nat.toHexDigits n len <|
      s.push (Nat.digitChar (b >>> 4).toNat) |>.push (Nat.digitChar (b &&& 15).toNat)

/-- Format hash as hex digit with extension `.ltar` -/
def UInt64.asLTar (n : UInt64) : String :=
  s!"{Nat.toHexDigits n.toNat 8}.ltar"

namespace Lean

/--
TODO: This is copied (without modification) from the Lean source. It should
be available in v4.17.0-rc1.
-/
partial def findLean (sp : SearchPath) (mod : Name) : IO System.FilePath := do
  if let some fname ← sp.findWithExt "lean" mod then
    return fname
  else
    let pkg := System.FilePath.mk <| mod.getRoot.toString (escape := false)
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

/-- Cleanup path with respect to components "", ".", and ".." -/
def clean (path : FilePath) : FilePath :=
  mkFilePath <| go path.components
where
  go : List String → List String
  | [] => []
  | "" :: path => go path
  | "." :: path => go path
  | ".." :: path => ".." :: go path
  | _ :: ".." :: path => go path
  | p :: ath => p :: go ath

/--
Test if the `target` path lies inside `parent`.

This is purely done by comparing the paths' components.
It does not have access to `IO` so it does not check if any paths actually exist.

The paths can contain arbitrary amounts of `"."`, `""` or `".."`.
However, if the paths do not contain the same amount of leading `".."`, it
will return `false`.
-/
def contains (parent target : FilePath) : Bool :=
  go parent.components target.components
where
  go : List String → List String → Bool
  -- ignore leading "." or ""
  | "." :: parent, target => go parent target
  | parent, "." :: target => go parent target
  | "" :: parent, target => go parent target
  | parent, "" :: target => go parent target
  -- must not start with unequal quantity of ".."
  | ".." :: parent, ".." :: target => go parent target
  | ".." :: _, _ => false
  | _, ".." :: _ => false
  -- cancel entry with following ".."
  | _ :: ".." :: parent, target => go parent target
  | parent, _ :: ".." :: target => go parent target
  -- base cases
  | [], _ => true
  | _ :: _, [] => false
  -- recursion
  | p :: arent, t :: arget => if p == t then go arent arget else false

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| go path.components parent.components
where
  go : List String → List String → List String
  | path@(x :: xs), y :: ys => if x == y then go xs ys else path
  | [], _ => []
  | path, [] => path

end System.FilePath
