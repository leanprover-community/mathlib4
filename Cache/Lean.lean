/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Arthur Paulino
-/

import Lean.Data.Name
import Lean.Util.Paths

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

-- copied from Mathlib
/-- Create a `Name` from a list of components. -/
def Lean.Name.fromComponents : List Name → Name := go .anonymous where
  go : Name → List Name → Name
  | n, []        => n
  | n, s :: rest => go (s.updatePrefix n) rest

namespace System.FilePath

/--
Normalize path and cleanup path with respect to components `""`, `"."`, and `".."`.
The result will not contain any `""` or `"."` and will only contain leading `".."`.

Note: `System.FilePath.normalize` might be expected to do most of this, but it doesn't currently.
-/
def clean (path : FilePath) : FilePath :=
  mkFilePath <| (goReversed path.normalize.components.reverse).reverse
where
  /--
  iterate backwards over the components and keep track of the number of `".."`
  that still need to be processed.
  -/
  goReversed (path : List String) (unprocessedParent : Nat := 0) : List String :=
    match path, unprocessedParent with
    -- add correct number of leading ".."
    -- note we should add them at the end, but since the `path` is guaranteed to be `[]`,
    -- it's equivalent - but faster - to add them in the front.
    | [], 0 => []
    | [], n+1 => ".." :: (goReversed [] n)
    -- found current directory reference, drop it
    | "." :: path, n => goReversed path n
    | "" :: path, n => goReversed path n
    -- found parent directory reference: increase counter
    | ".." :: path, n => goReversed path (n+1)
    -- found other component: decrease counter or add component to result
    | _ :: path, n+1 => goReversed path n
    | c :: path, 0 => c :: goReversed path 0

-- unit tests for `System.FilePath.clean`
#guard FilePath.clean "" == ""
#guard FilePath.clean "." == ""
#guard FilePath.clean ("." / ".") == ""
#guard FilePath.clean ("." / "") == ""
#guard FilePath.clean ("." / "A") == "A"
#guard FilePath.clean ("." / "..") == ".."
#guard FilePath.clean (".." / "..") == (".." / "..")
#guard FilePath.clean ("A" / ".." / "B") == "B"
#guard FilePath.clean ("A" / "." / "B") == ("A" / "B")
#guard FilePath.clean ("A" / "B" / "C" / ".." / ".." / ".." / "..") == ".."
#guard FilePath.clean ("A" / "B" / "C" / ".." / ".." / "." / ".." / "..") == ".."
#guard FilePath.clean ("A" / "B" / "C" / ".." / ".." / ".." / "D") == "D"

/--
Test if the `target` path lies inside `parent`.
This is purely done by comparing the paths' components.
It does not have access to `IO` so it does not check if any paths actually exist.
The paths can contain arbitrary amounts of `"."`, `""` or `".."`.
However, if the paths do not contain the same amount of leading `".."`, it
will return `false`.
-/
def contains (parent target : FilePath) : Bool :=
  go parent.clean.components target.clean.components
where
  go : List String → List String → Bool
  -- must start with equal quantity of ".."
  | ".." :: parent, ".." :: target => go parent target
  | ".." :: _, _ => false
  | _, ".." :: _ => false
  -- base cases
  -- cleaned paths do not contain `"."` anymore, but `[""]` is a valid path
  | [], _ => true
  | "" :: [], _ => true
  | _ :: _, [] => false
  | _ :: _, "" :: [] => false
  -- recursion
  | p :: arent, t :: arget => if p == t then go arent arget else false

-- unit tests for `System.FilePath.contains`
/-- info: true -/ #guard_msgs in #eval FilePath.contains "." "."
/-- info: true -/ #guard_msgs in #eval FilePath.contains "" ""
/-- info: true -/ #guard_msgs in #eval FilePath.contains ".." ".."
/-- info: true -/ #guard_msgs in #eval FilePath.contains (".."/ "..") (".." / "..")
/-- info: true -/ #guard_msgs in #eval FilePath.contains "" "."
/-- info: true -/ #guard_msgs in #eval FilePath.contains "." ""
/-- info: true -/ #guard_msgs in #eval FilePath.contains "" "A"
/-- info: true -/ #guard_msgs in #eval FilePath.contains "A" ("A" / ".." / "A")
/-- info: true -/ #guard_msgs in #eval FilePath.contains "A" ("B" / ".." / "A")
/-- info: true -/ #guard_msgs in #eval FilePath.contains ("A" / ".." / "A") ("A" / "C")
/-- info: true -/ #guard_msgs in #eval FilePath.contains ("B" / ".." / "A") ("A" / "C")
/-- info: true -/ #guard_msgs in #eval FilePath.contains ("A" / "B" / ".." / ".."/ "C") ("C" / "D")
/-- info: true -/ #guard_msgs in #eval FilePath.contains "C" ("A" / "B" / ".." / ".."/ "C")
/-- info: true -/ #guard_msgs in #eval FilePath.contains "A" ("A" / "B")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "." ".."
/-- info: false -/ #guard_msgs in #eval FilePath.contains "" ".."
/-- info: false -/ #guard_msgs in #eval FilePath.contains ".." "." -- false by convention
/-- info: false -/ #guard_msgs in #eval FilePath.contains ".." ""
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".."/ "..") ".."
/-- info: false -/ #guard_msgs in #eval FilePath.contains ".." (".." / "..")
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") "."
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") "A"
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" (".." / ".."/ "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B" / ".." / ".." / ".."/ "C") ("C" / "D")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B") "A"
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ("B" / "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B") ("A" / "C" / "B")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "." ("A" / "B" / "C" / ".." / ".." / ".." / ".." / "D")

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| go path.components parent.components
where
  go : List String → List String → List String
  | path@(x :: xs), y :: ys => if x == y then go xs ys else path
  | [], _ => []
  | path, [] => path

end System.FilePath
