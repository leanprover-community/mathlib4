/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka, Jon Eugster
-/

import Mathlib.Init

/-!

# Tools for Unicode Linter

The actual linter is defined in `TextBased.lean`.

This file provides all white-lists and other tools used by the linter.

## Main declarations

* `emojis`, `nonEmojis`: characters in these lists should always be followed by
  the correct variant-selector `UnicodeVariant.emoji` or `UnicodeVariant.text`.
  These variant-selector should not appear anywhere else.

-/

namespace Mathlib.Linter.TextBased.UnicodeLinter

/-- Following any unicode character, this indicates that the emoji-variant should be displayed -/
def UnicodeVariant.emoji := '\uFE0F'

/-- Following any unicode character, this indicates that the text-variant should be displayed -/
def UnicodeVariant.text := '\uFE0E'

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061". -/
def printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  match digits.length with  -- print at least 4 (could be more) hex characters using leading zeros
  | 1 => "U+000".append <| String.mk digits
  | 2 => "U+00".append <| String.mk digits
  | 3 => "U+0".append <| String.mk digits
  | _ => "U+".append <| String.mk digits

/-- Unicode symbols in mathlib that should always be followed by the emoji-variant selector. -/
def emojis := #[
'\u2705',        -- ✅️
'\u274C',        -- ❌️
 -- TODO "missing end of character literal" if written as '\u1F4A5'
 -- see https://github.com/leanprover/lean4/blob/4eea57841d1012d6c2edab0f270e433d43f92520/src/Lean/Parser/Basic.lean#L709
.ofNat 0x1F4A5,  -- 💥️
.ofNat 0x1F7E1,  -- 🟡️
.ofNat 0x1F4A1,  -- 💡️
.ofNat 0x1F419,  -- 🐙️
.ofNat 0x1F50D,  -- 🔍️
.ofNat 0x1F389,  -- 🎉️
'\u23F3',        -- ⏳️
.ofNat 0x1F3C1 ] -- 🏁️

/-- Unicode symbols in mathlib that should always be followed by the text-variant selector. -/
def nonEmojis : Array Char := #[]

end Mathlib.Linter.TextBased.UnicodeLinter
