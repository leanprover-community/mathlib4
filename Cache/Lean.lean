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
Normalize path and cleanup path with respect to components `""` and `"."`:

* Trailing sperarators and additional separators in the middle are both removed.
* A path might start with 0, 1, 2, or 3+ separators. 0-2 leading separators are
  kept in place, 3+ are reduced to one leading separator.
* `.` is stripped from the path unless it's the only no-separator character

Note: `System.FilePath.normalize` might be expected to do this, but it doesn't currently.

POSIX path spec: https://pubs.opengroup.org/onlinepubs/009695399/basedefs/xbd_chap03.html#tag_03_266
-/
def clean (path : FilePath) : FilePath :=
  mkFilePath <| match path.normalize.components with
    -- invalid path
    | [] => []
    -- fix number of leading separators, then clean the tail of the path
    | "" :: "" :: "" :: [] => "" :: "" :: "" :: []
    | "" :: "" :: "" :: p  => "" :: cleanTail (takeLeadingSep p) true
    | "" :: "" :: []       => "" :: "" :: []
    | "" :: "" :: p        => "" :: "" :: cleanTail (takeLeadingSep p) true
    | "" :: []             => "" :: []
    | "" :: p              => "" :: cleanTail (takeLeadingSep p) true
    | p                    => cleanTail p false
where
  /-- take any leading `""`. -/
  takeLeadingSep : List String → List String
    | [] => []
    | "" :: p => takeLeadingSep p
    | p => p
  /--
  Cleanup the tail of a path by removing any `""` and `"."` but special-case the paths
  `/`, `//` and `.`.

  - Assumes `path` does not start with `""` anymore.
  - `isAbs` determines if there will be leading separators appended to the cleaned tail.
    If `true`, then an empty path needs to be `""` in order to get  `/` or `//`.
    if `false`, the empty path needs to be `"."`, in order to get `.`
  -/
  cleanTail (path : List String) (isAbs : Bool) : List String :=
    match go path, isAbs with
      | [], true => [""]
      | [], false => ["."]
      | l, _ => l

  /-- drop all `"."` and all `""`. -/
  go : List String → List String
    | [] => []
    | "" :: path => go path
    | "." :: path => go path
    | p :: ath=> p :: go ath

-- unit tests for `System.FilePath.clean`
#guard FilePath.clean "" == ""               -- invalid path
#guard FilePath.clean "." == "."             -- cwd
-- remove trailing separators
-- > A pathname that contains at least one non-slash character and that ends with one or
-- > more trailing slashes shall be resolved as if a single dot character ( '.' ) were appended
-- > to the pathname.
#guard FilePath.clean "./" == "."
#guard FilePath.clean "A/B/" == "A" / "B"
#guard FilePath.clean "A/B/" == "A" / "B"
#guard FilePath.clean "A/B//" == "A" / "B"
#guard FilePath.clean "A/B///" == "A" / "B"
-- root directory
-- > A pathname consisting of a single slash shall resolve to the root directory of the process. […]
-- > A pathname that begins with two successive slashes may be interpreted in an
-- > implementation-defined manner, although more than two leading slashes shall
-- > be treated as a single slash.
#guard FilePath.clean "/." == "" / ""
#guard FilePath.clean "/./" == "" / ""
#guard FilePath.clean "/" == "" / ""
#guard FilePath.clean "//" == "" / "" / ""
#guard FilePath.clean "/A/B" == "" / "A" / "B"
#guard FilePath.clean "//A/B" == "" / "" / "A" / "B"
#guard FilePath.clean "///A/B" == "" / "A" / "B"
#guard FilePath.clean "////A/B" == "" / "A" / "B"
-- remove multiple sepratators in the middle
#guard FilePath.clean "A//B" == "A" / "B"
#guard FilePath.clean "A///B" == "A" / "B"
#guard FilePath.clean "A////B" == "A" / "B"
-- Deal with CWD
#guard FilePath.clean "./." == "."
#guard FilePath.clean "././././" == "."
#guard FilePath.clean "./A" == "A"
#guard FilePath.clean "././././A" == "A"
#guard FilePath.clean "A/./B" == "A" / "B"
#guard FilePath.clean "A/././B" == "A" / "B"
-- Deal with ".."
#guard FilePath.clean "/.." == "" / ".."
#guard FilePath.clean "./.." == ".."
#guard FilePath.clean ".././.." == ".." / ".."
#guard FilePath.clean "../.." == ".." / ".."
#guard FilePath.clean "A/../B" == "A" / ".." / "B"
#guard FilePath.clean ".//A//.././B" == "A" / ".." / "B"
-- real-world tests
#guard FilePath.clean "././././lean-toolchain" == "lean-toolchain"
#guard FilePath.clean "lean-toolchain" == "lean-toolchain"
#guard FilePath.clean ".lake/packages/mathlib/lean-toolchain" != "lean-toolchain"
#guard FilePath.clean "./.lake/packages/mathlib/lean-toolchain" != "lean-toolchain"

/-- Removes a parent path from the beginning of a path -/
def withoutParent (path parent : FilePath) : FilePath :=
  mkFilePath <| go path.components parent.components
where
  go : List String → List String → List String
  | path@(x :: xs), y :: ys => if x == y then go xs ys else path
  | [], _ => []
  | path, [] => path

end System.FilePath
