/-
Copyright (c) 2024 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka, Jon Eugster
-/
module

import Mathlib.Init


/-!

# Tools for the unicode Linter

The actual linter is defined in `TextBased.lean`.

This file defines the blocklist and other tools used by the linter.

-/

namespace Mathlib.Linter.TextBased.UnicodeLinter

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061". -/
public def printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  -- print at least 4 (could be more) hex characters using leading zeros
  ("U+".append <| "0000".drop digits.length |>.toString).append <| String.ofList digits

/-- Blocklist: If `false`, the character is not allowed in Mathlib. -/
public def isAllowedCharacter (c : Char) : Bool :=
  c != '\u00A0' -- non-breaking space

/-- Provide default replacement (`String`) for a blocklisted character, or `none` if none defined -/
public def replaceDisallowed : Char -> Option String
| '\u00a0' => " " -- replace non-breaking space with normal whitespace
| _ => none

-- TODO maybe remove this or move to unit-tests?
private theorem test_all_replaced_disallowed (c : Char) (creplaced : replaceDisallowed c ≠ none) :
    isAllowedCharacter c == false := by
  simp_all [isAllowedCharacter, replaceDisallowed]
  grind only

end Mathlib.Linter.TextBased.UnicodeLinter
