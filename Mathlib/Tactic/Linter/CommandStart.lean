/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Tactic.Linter.PPRoundtrip

/-!
#  The "commandStart" linter

The "commandStart" linter emits a warning if a command does not start on column `0`.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "commandStart" linter emits a warning if a command does not start on column `0`. -/
register_option linter.style.commandStart : Bool := {
  defValue := true
  descr := "enable the commandStart linter"
}

namespace Style.CommandStart

@[inherit_doc Mathlib.Linter.linter.style.commandStart]
def commandStartLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.style.commandStart (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  if let some pos := stx.getPos? then
    let colStart := ((← getFileMap).toPosition pos).column
    if colStart ≠ 0 then
      Linter.logLint linter.style.commandStart stx
        m!"'{stx}' starts on column {colStart}, \
          but all commands should start at the beginning of the line."
    if let some cmd := stx.find? (·.isOfKind ``Lean.Parser.Command.declaration) then
      let finalLintPos := match cmd.find? (·.isOfKind ``Lean.Parser.Term.typeSpec) with
        | some s => s.getPos?.getD default
        | none => match cmd.find? (·.isOfKind ``Lean.Parser.Command.declValSimple) with
          | some s => s.getPos?.getD default
          | none => default
      let stx := capSyntax stx finalLintPos.1 --(stx.getTailPos?.getD default).1
      let origSubstring : Substring := {stx.getSubstring?.getD default with stopPos := finalLintPos}
      let (real, lths) := polishSource origSubstring.toString
      let fmt ← (liftCoreM do PrettyPrinter.ppCategory `command stx <|> (do
        Linter.logLint linter.ppRoundtrip stx
          m!"The ppRoundtrip linter had some parsing issues: \
             feel free to silence it with `set_option linter.ppRoundtrip false in` \
             and report this error!"
        return real))
      let st := polishPP fmt.pretty
      if ! st.startsWith real then
        let diff := real.firstDiffPos st
        let pos := posToShiftedPos lths diff.1 + origSubstring.startPos.1
        let f := origSubstring.str.drop (pos)
        let extraLth := (f.takeWhile (· != st.get diff)).length
        let srcCtxt := zoomString real diff.1 5
        let ppCtxt  := zoomString st diff.1 5
        Linter.logLint linter.ppRoundtrip (.ofRange ⟨⟨pos⟩, ⟨pos + extraLth + 1⟩⟩)
          m!"Current syntax:  '{srcCtxt}'\nExpected syntax: '{ppCtxt}'\n"

initialize addLinter commandStartLinter

end Style.CommandStart

end Mathlib.Linter
