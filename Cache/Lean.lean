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
Normalize path and cleanup path with respect to components `""` and `"."`.

Note: `System.FilePath.normalize` might be expected to do this, but it doesn't currently.
-/
def clean (path : FilePath) : FilePath :=
  mkFilePath <| go path.normalize.components
where
  go : List String → List String
    | [] => []
    | "." :: path => go path
    | "" :: path => go path
    | c :: path => c :: go path

-- unit tests for `System.FilePath.clean`
#guard FilePath.clean "" == ""
#guard FilePath.clean "." == ""
#guard FilePath.clean ("." / ".") == ""
#guard FilePath.clean ("." / "") == ""
#guard FilePath.clean ("." / "A") == "A"
#guard FilePath.clean ("." / "..") == ".."
#guard FilePath.clean (".." / "." /"..") == (".." / "..")
#guard FilePath.clean (".." / "..") == (".." / "..")
#guard FilePath.clean ("A" / ".." / "B") == ("A" / ".." / "B")
#guard FilePath.clean ("." / "" / "A" / "" / ".." / "." / "B") == ("A" / ".." / "B")
#guard FilePath.clean ("A" / "." / "B") == ("A" / "B")

/--
Test if the `target` path lies inside `parent`.
This is purely done by comparing the paths' components.
It does not have access to `IO` so it does not check if any paths actually exist.
The paths can contain arbitrary amounts of `"."`, `""`.

If the `target` contains any `".."`, the result will only be `true` if these are
part of a shared prefix with `parent`,
i.e. `../A/..` contains `../A/../B` but not `../A/../B/../B`

-/
def contains (parent target : FilePath) : Bool :=
  go parent.clean.components target.clean.components
where
  go : List String → List String → Bool
    | [], [] => true
    -- cleaned paths do not contain `"."` anymore, but `[""]` is a valid path
    | "" :: parent, target => go parent target
    | parent, "" :: target => go parent target
    -- must start with equal quantity of ".."
    | ".." :: parent, ".." :: target => go parent target
    | ".." :: _, _ => false
    | _, ".." :: _ => false
    -- `parent` is longer
    | _ :: _, [] => false
    -- check `target` does not contain any more `..`
    | [], _ :: target => go [] target
    -- recursion
    | p :: arent, t :: arget => if p == t then go arent arget else false

-- unit tests for `System.FilePath.contains`
/-- info: true -/ #guard_msgs in #eval FilePath.contains "." "."
/-- info: true -/ #guard_msgs in #eval FilePath.contains "" ""
/-- info: true -/ #guard_msgs in #eval FilePath.contains "" "."
/-- info: true -/ #guard_msgs in #eval FilePath.contains "." ""
/-- info: true -/ #guard_msgs in #eval FilePath.contains "" "A"
/-- info: true -/ #guard_msgs in #eval FilePath.contains "." "A"
/-- info: true -/ #guard_msgs in #eval FilePath.contains "A" ("A" / "B")
/-- info: true -/ #guard_msgs in #eval FilePath.contains ".." ".."
/-- info: true -/ #guard_msgs in #eval FilePath.contains (".."/ "..") (".." / "..")
/-- info: true -/ #guard_msgs in #eval FilePath.contains ("A" / ".." / "B") ("A" / ".." / "B" / "C")
/-- info: true -/ #guard_msgs in #eval FilePath.contains ("A" / "..") ("A" / ".." / "A")
/-- info: true -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") (".." / "A" / ".." / "B")
/-- info: true -/ #guard_msgs in #eval FilePath.contains (".." / ".." / "A") (".." / ".." / "A" / "B")
/-- info: true -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") (".." / "A" / ".." / "B")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" "."
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ""
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ("B" / "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B") "A"
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B") ("A" / "C" / "B")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ("A" / ".." / "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ("A" / "B" / ".." / "B")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "." ".."
/-- info: false -/ #guard_msgs in #eval FilePath.contains "" ".."
/-- info: false -/ #guard_msgs in #eval FilePath.contains ".." "."
/-- info: false -/ #guard_msgs in #eval FilePath.contains ".." ""
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".."/ "..") ".."
/-- info: false -/ #guard_msgs in #eval FilePath.contains ".." (".." / "..")
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") "."
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") "A"
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ("A" / ".." / "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" ("B" / ".." / "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / ".." / "A") ("A" / "C")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("B" / ".." / "A") ("A" / "C")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B" / ".." / ".."/ "C") ("C" / "D")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "C" ("A" / "B" / ".." / ".."/ "C")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "A" (".." / ".."/ "A")
/-- info: false -/ #guard_msgs in #eval FilePath.contains ("A" / "B" / ".." / ".." / ".."/ "C") ("C" / "D")
/-- info: false -/ #guard_msgs in #eval FilePath.contains "." ("A" / "B" / "C" / ".." / ".." / ".." / ".." / "D")
/-- info: false -/ #guard_msgs in #eval FilePath.contains (".." / "A" / "..") (".." / "A" / ".." / "B" / ".." / "B")

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| go path.components parent.components
where
  go : List String → List String → List String
  | path@(x :: xs), y :: ys => if x == y then go xs ys else path
  | [], _ => []
  | path, [] => path

end System.FilePath
