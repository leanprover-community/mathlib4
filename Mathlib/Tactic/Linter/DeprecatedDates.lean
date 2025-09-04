/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Elab.Command
import Batteries.Data.String.Matcher
import Mathlib.Tactic.Linter.Header

/-!
# The "deprecatedDates" linter

The "deprecatedDates" linter emits a warning when consecutive deprecated declarations
have different dates but are not separated by a blank line.

When multiple declarations are deprecated, they should either:
- Have the same deprecation date (if they were deprecated together), or
- Be separated by a blank line (if they were deprecated at different times).

This helps maintain readability and makes the history of deprecations clearer.
-/

open Lean Elab Command Linter

namespace Mathlib.Linter

/-- The "deprecatedDates" linter emits a warning when consecutive deprecated declarations
have different dates but are not separated by a blank line. -/
register_option linter.style.deprecatedDates : Bool := {
  defValue := false
  descr := "enable the deprecatedDates linter"
}

namespace Style.DeprecatedDates

/-- Check if there's a blank line between two positions in the source. -/
def hasBlankLineBetween (fm : FileMap) (endPos : String.Pos) (startPos : String.Pos) : Bool :=
  if endPos ≥ startPos then
    false
  else
    let substring := { str := fm.source, startPos := endPos, stopPos := startPos : Substring }
    -- Split into lines and check if any line is empty (after trimming)
    substring.toString.split (· == '\n') |>.any (·.trim.isEmpty)

@[inherit_doc Mathlib.Linter.linter.style.deprecatedDates]
def deprecatedDatesLinter : Linter where
  run := withSetOptionIn fun stx ↦ do
    unless getLinterValue linter.style.deprecatedDates (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return

    -- Only check declaration commands
    unless [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind do
      return

    -- Get the declaration id directly from the syntax tree
    let declId :=
      if stx[1].isOfKind ``Lean.Parser.Command.instance then
        stx[1][3][0]
      else
        stx[1][1]
    if let .missing := declId then return

    -- Extract the declaration name with proper namespace handling
    let declName : Name :=
      if let `_root_ :: rest := declId[0].getId.components then
        rest.foldl (· ++ ·) default
      else (← getCurrNamespace) ++ declId[0].getId

    -- Check if this declaration has a deprecated attribute with a date
    let env ← getEnv
    let some info := Lean.Linter.deprecatedAttr.getParam? env declName
      | return -- Not deprecated
    let some currentDate := info.since?
      | return -- Deprecated but no date

    -- Get the file map for checking blank lines
    let fm ← getFileMap

    -- Get the position of the current declaration
    let some currentPos := stx.getPos? | return

    -- Look for the immediately previous declaration in the source
    -- by finding the last deprecated declaration before this position
    let sourceBeforeDecl := { str := fm.source, startPos := ⟨0⟩, stopPos := currentPos : Substring }
    let textBefore := sourceBeforeDecl.toString

    -- Find the immediately previous deprecated declaration
    -- Look for the last @[deprecated line before this declaration
    let lines := textBefore.split (· == '\n')

    -- Find the most recent @[deprecated line
    let mut foundPrevDeprecated := false
    let mut prevDate : Option String := none
    let mut prevDeprecatedLineIdx := 0

    for i in [:lines.length] do
      let lineIdx := lines.length - 1 - i  -- Go backwards
      if lineIdx >= 0 && lineIdx < lines.length then
        let line := lines[lineIdx]!
        if line.containsSubstr "@[deprecated" && line.containsSubstr "since" then
          -- Extract date from the line
          if let some startIdx := line.toList.findIdx? (fun c => c == '"') then
            let afterQuote := line.drop (startIdx + 1)
            if let some endIdx := afterQuote.toList.findIdx? (fun c => c == '"') then
              prevDate := some (afterQuote.take endIdx)
              foundPrevDeprecated := true
              prevDeprecatedLineIdx := lineIdx
              break

    if foundPrevDeprecated then
      if let some pd := prevDate then
        -- Check if there's a blank line between the previous deprecated line and current
        -- Skip the last line since it might be empty due to how we split the text
        let mut hasBlankLine := false
        let checkUntil := if lines.length > 0 then lines.length - 1 else lines.length
        for i in [prevDeprecatedLineIdx + 1:checkUntil] do
          if lines[i]!.trim.isEmpty then
            hasBlankLine := true
            break

        if pd != currentDate && !hasBlankLine then
          logLint linter.style.deprecatedDates stx
            m!"Consecutive deprecated declarations have different dates \
              ('{pd}' and '{currentDate}') but are not separated by a blank line"

initialize addLinter deprecatedDatesLinter

end Style.DeprecatedDates

end Mathlib.Linter
