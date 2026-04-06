/-
Copyright (c) 2024 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka, Jon Eugster, Michael Rothgang
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

/-- Blocklist: If `false`, the character is not allowed in Mathlib.
Note: if `true`, a character might still not be allowed depending on context
(e.g. misplaced variant selectors).
-/
public def isAllowedCharacter (c : Char) : Bool := !#[
'\u0009',     -- "TAB"
'\u000B',     -- "LINE TABULATION"
'\u000C',     -- "FORM FEED"
'\u000D',     -- "CARRIAGE RETURN" (note: CRLF is treated separately before `unicodeLinter` starts)
'\u001F',     -- "INFORMATION SEPARATOR ONE"
'\u00A0',     -- "NO-BREAK SPACE"
'\u1680',     -- "OGHAM SPACE MARK"
'\u2000',     -- "EN QUAD"
'\u2001',     -- "EM QUAD"
'\u2002',     -- "EN SPACE"
'\u2003',     -- "EM SPACE"
'\u2004',     -- "THREE-PER-EM SPACE"
'\u2005',     -- "FOUR-PER-EM SPACE"
'\u2006',     -- "SIX-PER-EM SPACE"
'\u2007',     -- "FIGURE SPACE"
'\u2008',     -- "PUNCTUATION SPACE"
'\u2009',     -- "THIN SPACE"
'\u200A',     -- "HAIR SPACE"
'\u200B',     -- "ZERO WIDTH SPACE"
'\u200C',     -- "ZERO WIDTH NON-JOINER"
'\u200D',     -- "ZERO WIDTH JOINER"
'\u200E',     -- "LEFT-TO-RIGHT MARK"
'\u200F',     -- "RIGHT-TO-LEFT MARK"
'\u2028',     -- "LINE SEPARATOR"
'\u2029',     -- "PARAGRAPH SEPARATOR"
'\u202A',     -- "LEFT-TO-RIGHT EMBEDDING"
'\u202B',     -- "RIGHT-TO-LEFT EMBEDDING"
'\u202C',     -- "POP DIRECTIONAL FORMATTING"
'\u202D',     -- "LEFT-TO-RIGHT OVERRIDE"
'\u202E',     -- "RIGHT-TO-LEFT OVERRIDE"
'\u202F',     -- "NARROW NO-BREAK SPACE"
'\u205F',     -- "MEDIUM MATHEMATICAL SPACE"
'\u2060',     -- "WORD JOINER"
'\u2062',     -- "INVISIBLE TIMES"
'\u2063',     -- "INVISIBLE SEPARATOR"
'\u2064',     -- "INVISIBLE PLUS"
'\u2066',     -- "LEFT-TO-RIGHT ISOLATE"
'\u2067',     -- "RIGHT-TO-LEFT ISOLATE"
'\u2068',     -- "FIRST STRONG ISOLATE"
'\u2069',     -- "POP DIRECTIONAL ISOLATE"
'\u206A',     -- "INHIBIT SYMMETRIC SWAPPING"
'\u206B',     -- "ACTIVATE SYMMETRIC SWAPPING"
'\u206C',     -- "INHIBIT ARABIC FORM SHAPING"
'\u206D',     -- "ACTIVATE ARABIC FORM SHAPING"
'\u206E',     -- "NATIONAL DIGIT SHAPES"
'\u206F',     -- "NOMINAL DIGIT SHAPES"
'\u3000'      -- "IDEOGRAPHIC SPACE"
  ].contains c

/-- Provide default replacement (`String`) for a blocklisted character, or `none` if none defined -/
public def replaceDisallowed : Char → Option String
| '\u0009' => "  "    -- "TAB" => "2 spaces"
| '\u000B' => "\n"    -- "LINE TABULATION" => "Line Feed"
| '\u000C' => "\n"    -- "FORM FEED" => "Line Feed"
| '\u000D' => "\n"    -- "CARRIAGE RETURN" => "Line Feed"
| '\u001F' => ""      -- "INFORMATION SEPARATOR ONE" => "nothing"
| '\u00A0' => " "     -- "NO-BREAK SPACE" => "1 space"
| '\u1680' => " "     -- "OGHAM SPACE MARK" => "1 space"
| '\u2000' => "  "    -- "EN QUAD" => "2 spaces"
| '\u2001' => "    "  -- "EM QUAD" => "4 spaces"
| '\u2002' => " "     -- "EN SPACE" => "1 space"
| '\u2003' => " "     -- "EM SPACE" => "1 space"
| '\u2004' => " "     -- "THREE-PER-EM SPACE" => "1 space"
| '\u2005' => " "     -- "FOUR-PER-EM SPACE" => "1 space"
| '\u2006' => " "     -- "SIX-PER-EM SPACE" => "1 space"
| '\u2007' => " "     -- "FIGURE SPACE" => "1 space"
| '\u2008' => " "     -- "PUNCTUATION SPACE" => "1 space"
| '\u2009' => " "     -- "THIN SPACE" => "1 space"
| '\u200A' => " "     -- "HAIR SPACE" => "1 space"
| '\u200B' => ""      -- "ZERO WIDTH SPACE" => "nothing"
| '\u200C' => ""      -- "ZERO WIDTH NON-JOINER" => "nothing"
| '\u200D' => ""      -- "ZERO WIDTH JOINER" => "nothing"
| '\u200E' => ""      -- "LEFT-TO-RIGHT MARK" => "nothing"
| '\u200F' => ""      -- "RIGHT-TO-LEFT MARK" => "nothing"
| '\u2028' => " "     -- "LINE SEPARATOR" => "1 space"
| '\u2029' => " "     -- "PARAGRAPH SEPARATOR" => "1 space"
| '\u202A' => ""      -- "LEFT-TO-RIGHT EMBEDDING" => "nothing"
| '\u202B' => ""      -- "RIGHT-TO-LEFT EMBEDDING" => "nothing"
| '\u202C' => ""      -- "POP DIRECTIONAL FORMATTING" => "nothing"
| '\u202D' => ""      -- "LEFT-TO-RIGHT OVERRIDE" => "nothing"
| '\u202E' => ""      -- "RIGHT-TO-LEFT OVERRIDE" => "nothing"
| '\u202F' => " "     -- "NARROW NO-BREAK SPACE" => "1 space"
| '\u205F' => " "     -- "MEDIUM MATHEMATICAL SPACE" => "1 space"
| '\u2060' => ""      -- "WORD JOINER" => "nothing"
| '\u2062' => ""      -- "INVISIBLE TIMES" => "nothing"
| '\u2063' => ""      -- "INVISIBLE SEPARATOR" => "nothing"
| '\u2064' => ""      -- "INVISIBLE PLUS" => "nothing"
| '\u2066' => ""      -- "LEFT-TO-RIGHT ISOLATE" => "nothing"
| '\u2067' => ""      -- "RIGHT-TO-LEFT ISOLATE" => "nothing"
| '\u2068' => ""      -- "FIRST STRONG ISOLATE" => "nothing"
| '\u2069' => ""      -- "POP DIRECTIONAL ISOLATE" => "nothing"
| '\u206A' => ""      -- "INHIBIT SYMMETRIC SWAPPING" => "nothing"
| '\u206B' => ""      -- "ACTIVATE SYMMETRIC SWAPPING" => "nothing"
| '\u206C' => ""      -- "INHIBIT ARABIC FORM SHAPING" => "nothing"
| '\u206D' => ""      -- "ACTIVATE ARABIC FORM SHAPING" => "nothing"
| '\u206E' => ""      -- "NATIONAL DIGIT SHAPES" => "nothing"
| '\u206F' => ""      -- "NOMINAL DIGIT SHAPES" => "nothing"
| '\u3000' => "  "    -- "IDEOGRAPHIC SPACE" =>  "2 spaces"
| _ => none

/-- Unicode symbols in mathlib that should always be followed by the emoji variant selector. -/
public def emojis : Array Char := #[
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

/-- Unicode symbols in mathlib that should always be followed by the text variant selector. -/
public def nonEmojis : Array Char := #[]

end Mathlib.Linter.TextBased.UnicodeLinter
