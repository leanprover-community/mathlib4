/-
Copyright (c) 2026 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
import Batteries
import Mathlib.Data.String.Defs

/-!
This script extracts all unique non-ascii characters from what is given via stdin
(and deliberately excludes a few).
It is designed to update the unicode character list in
`Mathlib/Tactic/Linter/TextBased/UnicodeLinter.lean`
from
https://github.com/leanprover/vscode-lean4/blob/master/lean4-unicode-input/src/abbreviations.json

Note: We should disallow any characters which cause right-to-left alignment.
For more information about Unicode's bidirectional classes, see
https://www.unicode.org/reports/tr44/tr44-34.html#Bidi_Class_Values
When using this script, **please manually check** any newly added characters conform to the guidelines,
see `Mathlib.Linter.TextBased.UnicodeLinter.withVSCodeAbbrev` and
`Mathlib.Linter.TextBased.UnicodeLinter.othersInMathlib`.

Note: this script will be used very rarely (if at all).
Therefore we probably shouldn't register it in `lakefile.lean` to avoid clutter.

Example usage:
```sh
URL="https://raw.githubusercontent.com/leanprover/vscode-lean4/refs/heads/master/lean4-unicode-input/src/abbreviations.json"
curl $URL | lake env lean --run scripts/extract-unique-nonascii.lean
```
-/

/-- We deliberately exclude some characters, based on the reasons noted. -/
def Char.manuallyExcluded (c : Char) : Bool :=
  c ∈ [
    '\u2001', -- \quad (U+2001) (due to being non-standard whitespace)
    '\uFDFC', -- RIAL sign (U+FDFC) (due to triggering right-aligned text).
    '\u060B', -- AFGHANI sign (U+060B) (due to triggering right-aligned text)
    '\u0332' -- COMBINING LOW LINE (U+0332) (due to modifying characters around it)
  ]

/-- We deliberately exclude some characters. -/
def Char.allowedNonAscii (c : Char) : Bool :=
    !c.isAscii && !c.manuallyExcluded

def reprCharsChunked (xs : List Char) (chunkSize : Nat := 16) : String :=
  let elems := xs.map (fun c => "'" ++ String.singleton c ++ "'")
  let lines :=
    elems
      |>.toChunks chunkSize
      |>.map (fun chunk => String.intercalate ", " chunk)
  "[" ++ String.intercalate ",\n" lines ++ "]"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let allText ← stdin.readToEnd
  let manuallyExcluded := (allText.toList.filter Char.manuallyExcluded).eraseDups
  IO.println s!"Manually excluded these carachters:"
  IO.println s!"{reprCharsChunked manuallyExcluded}"
  let outputList := (allText.toList.filter Char.allowedNonAscii).eraseDups
  IO.println s!"Found {outputList.length} valid unique non-ascii characters:"
  IO.println s!"{reprCharsChunked outputList}"
