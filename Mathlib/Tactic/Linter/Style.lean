/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
## Style linters

This file contains (currently one, eventually more) linters about stylistic aspects:
these are only about coding style, but do not affect correctness nor global coherence of mathlib.

Historically, these were ported from the `lint-style.py` Python script.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The `setOption` linter emits a warning on a `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option. -/
register_option linter.setOption : Bool := {
  defValue := false
  descr := "enable the `setOption` linter"
}

namespace Style.SetOption

/-- Whether a syntax element is a `set_option` command, tactic or term:
Return the name of the option being set, if any. -/
def parse_set_option : Syntax → Option Name
  -- This handles all four possibilities of `_val`: a string, number, `true` and `false`.
  | `(command|set_option $name:ident $_val) => some name.getId
  | `(set_option $name:ident $_val in $_x) => some name.getId
  | `(tactic|set_option $name:ident $_val in $_x) => some name.getId
  | _ => none

/-- Whether a given piece of syntax is a `set_option` command, tactic or term. -/
def is_set_option : Syntax → Bool :=
  fun stx ↦ parse_set_option stx matches some _name

/-- The `setOption` linter: this lints any `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option.

**Why is this bad?** These options are good for debugging, but should not be
used in production code.
**How to fix this?** Remove these options: usually, they are not necessary for production code.
(Some tests will intentionally use one of these options; in this case, simply allow the linter.)
-/
def setOptionLinter : Linter where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.setOption (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some head := stx.find? is_set_option then
      if let some name := parse_set_option head then
        let forbidden := [`debug, `pp, `profiler, `trace]
        if forbidden.contains name.getRoot then
          Linter.logLint linter.setOption head
            m!"Setting options starting with '{"', '".intercalate (forbidden.map (·.toString))}' \
               is only intended for development and not for final code. \
               If you intend to submit this contribution to the Mathlib project, \
               please remove 'set_option {name}'."

initialize addLinter setOptionLinter

end Style.SetOption


/-!
# The "missing end" linter

The "missing end" linter emits a warning on non-closed `section`s and `namespace`s.
It allows the "outermost" `noncomputable section` to be left open (whether or not it is named).
-/

open Lean Elab Command

/-- The "missing end" linter emits a warning on non-closed `section`s and `namespace`s.
It allows the "outermost" `noncomputable section` to be left open (whether or not it is named).
-/
register_option linter.missingEnd : Bool := {
  defValue := false
  descr := "enable the missing end linter"
}

namespace Style.MissingEnd

@[inherit_doc Mathlib.Linter.linter.missingEnd]
def missingEndLinter : Linter where run := withSetOptionIn fun stx ↦ do
    -- Only run this linter at the end of a module.
    unless stx.isOfKind ``Lean.Parser.Command.eoi do return
    if Linter.getLinterValue linter.missingEnd (← getOptions) &&
        !(← MonadState.get).messages.hasErrors then
      let sc ← getScopes
      -- The last scope is always the "base scope", corresponding to no active `section`s or
      -- `namespace`s. We are interested in any *other* unclosed scopes.
      if sc.length == 1 then return
      let ends := sc.dropLast.map fun s ↦ (s.header, s.isNoncomputable)
      -- If the outermost scope corresponds to a `noncomputable section`, we ignore it.
      let ends := if ends.getLast!.2 then ends.dropLast else ends
      -- If there are any further un-closed scopes, we emit a warning.
      if !ends.isEmpty then
        let ending := (ends.map Prod.fst).foldl (init := "") fun a b ↦
          a ++ s!"\n\nend{if b == "" then "" else " "}{b}"
        Linter.logLint linter.missingEnd stx
         m!"unclosed sections or namespaces; expected: '{ending}'"

initialize addLinter missingEndLinter

end Style.MissingEnd

/-!
# The `cdot` linter

The `cdot` linter is a syntax-linter that flags uses of the "cdot" `·` that are achieved
by typing a character different from `·`.
For instance, a "plain" dot `.` is allowed syntax, but is flagged by the linter.
-/

/--
The `cdot` linter flags uses of the "cdot" `·` that are achieved by typing a character
different from `·`.
For instance, a "plain" dot `.` is allowed syntax, but is flagged by the linter. -/
register_option linter.cdot : Bool := {
  defValue := false
  descr := "enable the `cdot` linter"
}

/-- `isCDot? stx` checks whether `stx` is a `Syntax` node corresponding to a `cdot` typed with
the character `·`. -/
def isCDot? : Syntax → Bool
  | .node _ ``cdotTk #[.node _ `patternIgnore #[.node _ _ #[.atom _ v]]] => v == "·"
  | .node _ ``Lean.Parser.Term.cdot #[.atom _ v] => v == "·"
  | _ => false

/--
`findCDot stx` extracts from `stx` the syntax nodes of `kind` `Lean.Parser.Term.cdot` or `cdotTk`. -/
partial
def findCDot : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findCDot).flatten
    match kind with
      | ``Lean.Parser.Term.cdot | ``cdotTk=> dargs.push stx
      | _ =>  dargs
  |_ => #[]

/-- `unwanted_cdot stx` returns an array of syntax atoms within `stx`
corresponding to `cdot`s that are not written with the character `·`.
This is precisely what the `cdot` linter flags.
-/
def unwanted_cdot (stx : Syntax) : Array Syntax :=
  (findCDot stx).filter (!isCDot? ·)

namespace Style.CDotLinter

@[inherit_doc linter.cdot]
def cdotLinter : Linter where run := withSetOptionIn fun stx => do
    unless Linter.getLinterValue linter.cdot (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in unwanted_cdot stx do
      Linter.logLint linter.cdot s m!"Please, use '·' (typed as `\\.`) instead of '{s}' as 'cdot'."

initialize addLinter cdotLinter

end Style.CDotLinter

/-!
# The `dollarSyntax` linter

The `dollarSyntax` linter flags uses of `<|` that are achieved by typing `$`.
-/

/-- The `dollarSyntax` linter flags uses of `<|` that are achieved by typing `$`. -/
register_option linter.dollarSyntax : Bool := {
  defValue := false
  descr := "enable the `dollarSyntax` linter"
}

namespace Style.dollarSyntax

/-- `findDollarSyntax stx` extracts from `stx` the syntax nodes of `kind` `$`. -/
partial
def findDollarSyntax : Syntax → Array Syntax
  | stx@(.node _ kind args) =>
    let dargs := (args.map findDollarSyntax).flatten
    match kind with
      | ``«term_$__» => dargs.push stx
      | _ => dargs
  |_ => #[]

@[inherit_doc linter.dollarSyntax]
def dollarSyntaxLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.dollarSyntax (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    for s in findDollarSyntax stx do
      Linter.logLint linter.dollarSyntax s m!"Please use '<|' and not '$' for the pipe operator."

initialize addLinter dollarSyntaxLinter

end Style.dollarSyntax

/-! # The "longLine linter" -/

/-- The "longLine" linter emits a warning on lines longer than 100 characters.
We allow lines containing URLs to be longer, though. -/
register_option linter.longLine : Bool := {
  defValue := false
  descr := "enable the longLine linter"
}

namespace Style.longLine

@[inherit_doc Mathlib.Linter.linter.longLine]
def longLineLinter : Linter where run := withSetOptionIn fun stx ↦ do
    unless Linter.getLinterValue linter.longLine (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    -- The linter ignores the `#guard_msgs` command, in particular its doc-string.
    -- The linter still lints the message guarded by `#guard_msgs`.
    if stx.isOfKind ``Lean.guardMsgsCmd then
      return
    -- if the linter reached the end of the file, then we scan the `import` syntax instead
    let stx := ← do
      if stx.isOfKind ``Lean.Parser.Command.eoi then
        let fileMap ← getFileMap
        -- `impMods` is the syntax for the modules imported in the current file
        let (impMods, _) ← Parser.parseHeader
          { input := fileMap.source, fileName := ← getFileName, fileMap := fileMap }
        return impMods
      else return stx
    let sstr := stx.getSubstring?
    let fm ← getFileMap
    let longLines := ((sstr.getD default).splitOn "\n").filter fun line =>
      (100 < (fm.toPosition line.stopPos).column)
    for line in longLines do
      if (line.splitOn "http").length ≤ 1 then
        Linter.logLint linter.longLine (.ofRange ⟨line.startPos, line.stopPos⟩)
          m!"This line exceeds the 100 character limit, please shorten it!"

initialize addLinter longLineLinter

end Style.longLine

end Mathlib.Linter
