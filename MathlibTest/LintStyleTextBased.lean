import Mathlib.Tactic.Linter.TextBased
import Batteries.Data.List.Basic

section unicodeLinter

open Mathlib.Linter.TextBased
open Mathlib.Linter.TextBased.UnicodeLinter

-- test parsing back error message in `parse?_errorContext` for variant selector errors

-- "missing" selector
#guard let errContext : ErrorContext := {
    error := .unicodeVariant "\u1234A" UnicodeVariant.emoji ⟨6⟩,
    lineNumber := 4, path:="./MYFILE.lean"}
  (parse?_errorContext <| outputMessage errContext .exceptionsFile) == some errContext

-- "wrong" selector
#guard let errContext : ErrorContext := {
    error := .unicodeVariant "\u1234\uFE0E" UnicodeVariant.emoji ⟨6⟩,
    lineNumber := 4, path:="./MYFILE.lean"}
  (parse?_errorContext <| outputMessage errContext .exceptionsFile) == some errContext

-- "unexpected" selector
#guard let errContext : ErrorContext := {
    error := .unicodeVariant "\uFE0EA" none ⟨6⟩, lineNumber := 4, path:="./MYFILE.lean"}
  (parse?_errorContext <| outputMessage errContext .exceptionsFile) == some errContext

-- only one variant selector can be used
#guard emojis.toList ∩ nonEmojis.toList = ∅

end unicodeLinter
