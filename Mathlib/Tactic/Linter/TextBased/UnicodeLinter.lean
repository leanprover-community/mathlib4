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

-- TODO when moving this to `MathlibTest/LintStyle.lean`, `grind` crashes with
--     >>  invalid pattern(s) for `replaceDisallowed.match_1.congr_eq_2`
--   No idea what that means... What to do? Options:
--   Delete this? Leave it here? Fix the error and move to tests?
private theorem disallowed_of_replaceable (c : Char) (creplaced : replaceDisallowed c ≠ none) :
    isAllowedCharacter c == false := by
  simp_all only [replaceDisallowed, ne_eq, isAllowedCharacter, ↓Char.isValue, beq_false,
    Bool.not_eq_eq_eq_not, Bool.not_true, bne_eq_false_iff_eq]
  grind only

end Mathlib.Linter.TextBased.UnicodeLinter
