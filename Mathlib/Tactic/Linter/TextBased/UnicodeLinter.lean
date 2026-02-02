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

/-- Following any unicode character, this indicates that the emoji variant should be displayed -/
public def UnicodeVariant.emoji := '\uFE0F'

/-- Following any unicode character, this indicates that the text variant should be displayed -/
public def UnicodeVariant.text := '\uFE0E'

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061". -/
public def Char.printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  -- print at least 4 (could be more) hex characters using leading zeros
  ("U+".append <| "0000".drop digits.length |>.toString).append <| String.ofList digits

/-- Prints all characters in a string in hexadecimal with prefix 'U+'.
E.g., "ab" is "U+0061;U+0062". -/
public def String.printCodepointHex (s : String) : String :=
  -- note: must not contain spaces because of the error message parsing below!
  ";".intercalate <| s.toList.map Char.printCodepointHex

/-- If `false`, the character is not allowed in Mathlib. -/
public def isAllowedCharacter (c : Char) : Bool :=
  !#['\u00A0'].contains c -- non-breaking space

/-- Provide default replacement (`String`) for a blocklisted character, or `none` if not defined -/
public def replaceDisallowed : Char → Option String
| '\u00a0' => " " -- replace non-breaking space with normal whitespace
| _ => none

/-- A unicode character is in this list
if and only if it should always be followed by the emoji variant selector. -/
public def emojis := #[
'\u2705',        -- ✅️
'\u274C',        -- ❌️
 -- Note: cannot write these as e.g. '\u1F4A5' due to error: "missing end of character literal"
.ofNat 0x1F4A5,  -- 💥️
.ofNat 0x1F7E1,  -- 🟡️
.ofNat 0x1F4A1,  -- 💡️
.ofNat 0x1F419,  -- 🐙️
.ofNat 0x1F50D,  -- 🔍️
.ofNat 0x1F389,  -- 🎉️
'\u23F3',        -- ⏳️
.ofNat 0x1F3C1,  -- 🏁️
]

/-- A unicode character is in this list
if and only if it should always be followed by the text variant selector. -/
public def nonEmojis : Array Char := #[]

end Mathlib.Linter.TextBased.UnicodeLinter
