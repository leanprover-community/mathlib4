/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Lean.Linter.Util
import Batteries.Data.String.Basic

/-!
## Style linters

Linters which are purely about stylistic things: ported from the `lint-style.py` script.
-/

open Lean Elab Command

namespace Mathlib.Linter.Style.SetOption

/-- Whether a syntax element is a `set_option` call:
Return the name of the option being set, if any. -/
def parse_set_option : Syntax → Option (Ident)
  -- This handles all four cases: string, number, true and false
  | `(command|set_option $name:ident $_val) => some name
  | `(set_option $name:ident $_val in $_x) => some name
  | `(tactic|set_option $name:ident $_val in $_x) => some name
  | _ => none

/-- Whether a given piece of syntax is a `set_option` command, tactic or term. -/
def is_set_option : Syntax → Bool :=
  fun stx ↦ parse_set_option stx matches some _name

/-- The `setOption` linter emits a warning on a `set_option ...`. -/
register_option linter.setOption : Bool := {
  defValue := true
  descr := "enable the `setOption` linter"
}

/-- Gets the value of the `linter.setOption` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.setOption o

/-- The `setOption` linter: this lints any `set_option` command, term or tactic
which sets a `pp`, `profiler` or `trace` option.

**Why is this bad?** These options are good for debugging, but should not be
used in production code.
-/
def setOptionLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match stx.findStack? (fun _ ↦ true) is_set_option with
    | some ((head, _n)::_chain) =>
      match parse_set_option head with
      | some (name) =>
        -- Drop a leading `
        let name := (toString name).drop 1
        if name.startsWith "pp." || name.startsWith "profiler." || name.startsWith "trace." then
          Linter.logLint linter.setOption head m!"Forbidden set_option `{name}`; please remove"
      | _ => return
    | _ => return

initialize addLinter setOptionLinter

end Mathlib.Linter.Style.SetOption

namespace Mathlib.Linter.Style.BroadImport

/-- Return with a string is a correct-looking authors like in a copyright header. -/
def is_correct_authors_line (line : String) : Bool :=
  -- We cannot reasonably validate the author names, so we look only for the three common mistakes:
  -- the file starting wrong, using ' and ' between names, and a '.' at the end of line.
  !(line.startsWith "Authors: " && line.containsSubstr "  "
    && line.containsSubstr " and " && line.endsWith ".")

def toOptionWithDefault {α : Type} (a : α) : Bool → Option α :=
  fun b ↦ match b with
    | true => some a
    | false => none

/-- Given two `Option Int`, computes the minimal value contained in them. -/
def option_min (a b : Option Int) : Option Int :=
    match (a, b) with
    | (some a, some b) => some (min a b)
    | (some a, none) => some a
    | (none, x) => x

/-- Like `option_min`, but for four arguments. -/
def option_min4 (a b c d : Option Int) := option_min (option_min a b) (option_min c d)

/-- Lint a collection of input lines if they are missing an appropriate copyright header.

A copyright header should start at the very beginning of the file and contain precisely five lines,
including the copy year and holder, the license and main author(s) of the file (in this order).
-/
def copyright_header(lines : Array String) : Option Int := do
  -- Unlike the Python script, we just emit one warning.
  let start := lines.extract 0 4
  -- The header should start and end with blank comments.
  let start_end := match (start.get? 0, start.get? 4) with
  | (some "/-", some "-/") => none
  | (some "/-", _) => some 4
  | _ => some 0
  -- The first real line should be a copyright.
  let copyright_matches : Bool := if let some copy := (start.get? 1) then
    copy.startsWith "Copyright (c) " && copy.endsWith ". All rights reserved."
  else
    false
  let copy := toOptionWithDefault 3 copyright_matches
  -- The second line should be standard.
  let second_line := match start.get? 2 with
   | "Released under Apache 2.0 license as described in the file LICENSE." => none
   | _ => some 3
  -- The third line should contain authors.
  let authors_match := match start.get? 3 with
      | some line => line.containsSubstr "Author"
      | none => false
  let authors_match := match authors_match with
   | true => some 3
   | false => none
  let result := option_min4 start_end copy second_line authors_match
  -- If it does, we check that author formatting is right.
  if let some line := start.get? 3  then
    if !is_correct_authors_line line then
      -- new error for malformed authors line
      let sdf := 42
  result
  -- xxx: is there a nicer way to do the options/bool manipulation
-- optional: include module docstring code
--         words = line.split()
--         if words[0] != "import" and words[0] != "--" and words[0] != "/-!" and words[0] != "#align_import":
--             errors += [(ERR_MOD, line_nr, path)]
--             break
--         if words[0] == "/-!":
--             break
--     return errors, lines
