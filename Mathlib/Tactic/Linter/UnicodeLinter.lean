/-
Copyright (c) 2024 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka, Jon Eugster
-/

import Mathlib.Init

/-!

# Tools for Unicode Linter

The actual linter is defined in `TextBased.lean`.

This file provides all white-lists and other tools used by the linter.

-/

namespace Mathlib.Linter.TextBased.UnicodeLinter

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061". -/
def printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  match digits.length with  -- print at least 4 (could be more) hex characters using leading zeros
  | 1 => "U+000".append <| String.mk digits
  | 2 => "U+00".append <| String.mk digits
  | 3 => "U+0".append <| String.mk digits
  | _ => "U+".append <| String.mk digits

/-- If `false` the character is not allowed in Mathlib.
-/
def isAllowedCharacter (c : Char) : Bool :=
  c != '\u00A0' -- non-breaking space

end Mathlib.Linter.TextBased.UnicodeLinter
