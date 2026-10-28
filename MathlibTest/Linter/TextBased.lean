module

import all Batteries.Data.List.Basic
import all Mathlib.Tactic.Linter.TextBased
import all Mathlib.Tactic.Linter.TextBased.UnicodeLinter

/-!
# Tests for mathlib's text-based linters
-/

section unicodeLinter

open Mathlib.Linter.TextBased
open Mathlib.Linter.TextBased.UnicodeLinter

/- A character either does or doesn't have an abbreviation in the VSCode extension. -/
#guard withVSCodeAbbrev.toList ∩ othersInMathlib.toList = ∅

/- No character is both an emoji and not an emoji. -/
#guard emojis.toList ∩ nonEmojis.toList = ∅

/- No character is both an emoji and unrestricted. -/
#guard emojis.toList ∩ unrestricted.toList = ∅

/- No character is both a non-emoji and unrestricted. -/
#guard nonEmojis.toList ∩ unrestricted.toList = ∅

def allLinterDefinedCharacterLists : List (List Char) := [
  withVSCodeAbbrev,
  othersInMathlib,
  emojis,
  nonEmojis,
  unrestricted
].map Array.toList

/- Ensure none of the lists contain duplicates -/
#guard allLinterDefinedCharacterLists.all <| (List.Pairwise (· != ·) ·)

/- See [Private Use Area](https://en.wikipedia.org/wiki/Private_Use_Areas). -/
def isPrivateUseAreaChar (c : Char) : Bool :=
  letI N := c.toNat
  (0xE000 ≤ N && N ≤ 0xF8FF) ||
  (0xF0000 ≤ N && N ≤ 0xFFFFF) ||
  (0x100000 ≤ N && N ≤ 0x10FFFF)

/- Ensure no list contains [Private Use Area](https://en.wikipedia.org/wiki/Private_Use_Areas) characters. -/
#guard !(allLinterDefinedCharacterLists.any <| (List.any · isPrivateUseAreaChar))

/-!
Ensure parsing back error messages in `parse?_errorContext` works.

**These tests guard against changes in the error message.**
Changes to the error message may mean the indices in `parse?_errorContext` need to be adjusted
-/

-- This tests if the offending character appears in the error message at the expected position.
-- This position is also used by `parse?_errorContext`
-- If the error message is changed, the index used there and also here will also need to change.
-- Since `parse?_errorContext` is also tested below, this test is strictly speaking redundant.
-- It can be used to find the correct index.
/-- info: some "'X'" -/
#guard_msgs in
#eval (StyleError.errorMessage (.unwantedUnicode 'X') |>.splitToList (· == ' '))[12]?

/-- info: some "Missing" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval ((StyleError.errorMessage (.unicodeVariant "A" (some emoji))).splitToList (· == ' '))[0]?

/-- info: some "Wrong" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval
  ((StyleError.errorMessage (.unicodeVariant "A\uFE0F" (some emoji))).splitToList (· == ' '))[0]?

/-- info: some "Unexpected" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval ((StyleError.errorMessage (.unicodeVariant "A\uFE0F" none)).splitToList (· == ' '))[0]?

/-- info: some "\"AB\"" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval ((StyleError.errorMessage (.unicodeVariant "AB" (some emoji))).splitToList (· == ' '))[4]?

/-- info: some "\"AB\"" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval
  ((StyleError.errorMessage (.unicodeVariant "AB" (some emoji))).splitToList (· == ' '))[4]?

/-- info: some "\"AB\"" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval ((StyleError.errorMessage (.unicodeVariant "AB" none)).splitToList (· == ' '))[4]?

/-- info: some "emoji" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval ((StyleError.errorMessage (.unicodeVariant "AB" (some emoji))).splitToList (· == ' '))[9]?

/-- info: some "emoji" -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval
  ((StyleError.errorMessage (.unicodeVariant "AB" (some emoji))).splitToList (· == ' '))[9]?

/-- info: none -/
#guard_msgs in
open UnicodeLinter.UnicodeVariant in
#eval ((StyleError.errorMessage (.unicodeVariant "AB" none)).splitToList (· == ' '))[9]?

-- Testing that error messages can be parsed back correctly

meta instance : ToString StyleError where
  toString error := match error with
    | .unwantedUnicode char => s!"{error.errorCode}: {char}"
    | .unicodeVariant s none =>
      s!"{error.errorCode}: {(" ".intercalate <| s.toList.map Char.printCodepointHex)} (none)"
    | .unicodeVariant s (some sel) =>
      s!"{error.errorCode}: {(" ".intercalate <| s.toList.map Char.printCodepointHex)} \
        ({Char.printCodepointHex sel})"
    | other => s!"{other.errorCode}"

meta instance : ToString ErrorContext where
  toString error := s!"{error.error}:l.{error.lineNumber}, {error.path}"

meta def ErrorContext.isValid_parse?_error_context (ec : ErrorContext) : Bool :=
  let msg := outputMessage ec .exceptionsFile
  -- -- print error message for debugging
  -- dbg_trace msg
  match parse?_errorContext <| msg with
  | none => False
  | some parsed =>
    ec == parsed

#guard ErrorContext.isValid_parse?_error_context {
  error := .adaptationNote,
  lineNumber := 1234, path:="Mathlib/Tactic/Measurability/Init.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .windowsLineEnding,
  lineNumber := 1234, path:="Mathlib/Tactic/Measurability/Init.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .semicolon,
  lineNumber := 1234, path := "Mathlib/Tactic/Measurability/Init.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .unwantedUnicode '\u1234',
  lineNumber := 1234, path:="./MYFILE.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .unwantedUnicode '\u00a0',
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

-- "missing" variant selector
#guard ErrorContext.isValid_parse?_error_context {
  error := .unicodeVariant "\u271d" UnicodeVariant.emoji,
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .unicodeVariant "\u271d" UnicodeVariant.text,
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

-- "wrong" variant selector
#guard ErrorContext.isValid_parse?_error_context {
  error := .unicodeVariant "\u271d\uFE0E" UnicodeVariant.emoji,
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .unicodeVariant "\u271d\uFE0F" UnicodeVariant.text,
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

-- "unexpected" variant selector
#guard ErrorContext.isValid_parse?_error_context {
  error := .unicodeVariant "\u271d\uFE0E" none,
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

#guard ErrorContext.isValid_parse?_error_context {
  error := .unicodeVariant "\u271d\uFE0F" none,
  lineNumber := 22, path:="Mathlib/Tactic/Measurability/Init.lean"}

/-- An error in this proof could mean that `replaceDisallowed` contains a character
which is not disallowed by `isAllowedCharacter`. -/
private theorem disallowed_of_replaceable (c : Char) (creplaced : replaceDisallowed c ≠ none) :
    !isAllowedCharacter c := by
  unfold replaceDisallowed at creplaced
  split at creplaced <;>
  first
  | native_decide
  | exact absurd rfl creplaced

end unicodeLinter
