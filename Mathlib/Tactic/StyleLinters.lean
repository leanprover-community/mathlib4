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

/-- Lint a collection of input strings if one of them contains an unnecessary broad import.
Return `none` if no import was found, and `some n` if such an import was on line `n` (1-based). -/
def contains_broad_imports(lines : Array String) : Option Int := do
  -- TODO: pass in the line number also

  -- All import statements must be placed "at the beginning" of the file:
  -- we can have any number of blank lines, imports and single or multi-line comments.
  -- Doc comments, however, are not allowed: there is no item they could document.
  let mut in_doc_comment : Bool := False
  for line in lines do
    if in_doc_comment then
      if line.endsWith "-/" then
        in_doc_comment := False
    else
      if let some (rest) := line.dropPrefix? "import " then
          -- If there is any in-line or beginning doc comment on that line, trim that.
          -- HACK: just split the string on space, "/" and "-";
          -- none of these occur in the module name so this is safe.
          if let some (name) := ((toString rest).split fun c ↦ (" /-".contains c)).head? then
            if name == "Mathlib.Tactic" then
              -- TODO: log an error, need the right monad context...
      -- If this is just a single-line comment (starts with "--"), just continue.
      if line.startsWith "/-" then
        in_doc_comment := True
  none

/-- Lint a collection of input lines if they are missing an appropriate copyright header. -/
def copyright_header(lines : Array String) : Option Int := do
-- TODO: pass in line numbers also, or enumerate internally
  let mut copy_started : Bool := False
  let mut copy_done : Bool := False
  for line in lines do
    if !copy_started then
      if line == "\n" then
        -- error: copyright, with line number and path
        let sdf := 42
      else
        if line == "/-\n" then
          copy_started := true
          --copy_start_line_nr = line_nr
    else
      -- error errors += [(ERR_COP, line_nr, path)]
      let foo := 42
  return 42


-- def regular_check(lines, path):
--     errors = []
--     copy_started = False
--     copy_done = False
--     copy_start_line_nr = 1
--     copy_lines = ""
--     for line_nr, line in lines:
--         if not copy_started and line == "\n":
--             errors += [(ERR_COP, copy_start_line_nr, path)]
--             continue
--         if not copy_started and line == "/-\n":
--             copy_started = True
--             copy_start_line_nr = line_nr
--             continue
--         if not copy_started:
--             errors += [(ERR_COP, line_nr, path)]
--         if copy_started and not copy_done:
--             copy_lines += line
--             if "Author" in line:
--                 # Validating names is not a reasonable thing to do,
--                 # so we just look for the two common variations:
--                 # using ' and ' between names, and a '.' at the end of line.
--                 if ((not line.startswith("Authors: ")) or
--                     ("  " in line) or
--                     (" and " in line) or
--                     (line[-2] == '.')):
--                     errors += [(ERR_AUT, line_nr, path)]
--             if line == "-/\n":
--                 if ((not "Copyright" in copy_lines) or
--                     (not "Apache" in copy_lines) or
--                     (not "Authors: " in copy_lines)):
--                     errors += [(ERR_COP, copy_start_line_nr, path)]
--                 copy_done = True
--             continue
--         if copy_done and line == "\n":
--             continue
--         words = line.split()
--         if words[0] != "import" and words[0] != "--" and words[0] != "/-!" and words[0] != "#align_import":
--             errors += [(ERR_MOD, line_nr, path)]
--             break
--         if words[0] == "/-!":
--             break
--     return errors, lines




def check_all_files : IO Bool := do
  -- Read all module names in Mathlib from `Mathlib.lean`.
  let all_names ← IO.FS.lines (System.mkFilePath [(toString "Mathlib.lean")])
  for line in all_names do
  -- Convert the module name to a file name.
    let path := System.mkFilePath ((line.split fun c ↦ (c == '.')).append [".lean"])
  -- Check of that file's contains a broad imports.
    let lines ← IO.FS.lines path
    if let some n := (contains_broad_imports lines) then
      --logInfo "boo"--println! "boo"
      return false
  pure true


-- parse_imports; see my file
-- if not in a comment
-- "import Mathlib.Tactic" is bad

/-- The `broadImport` linter emits a warning on an `import Mathlib.Tactic` statement. -/
register_option linter.broadImport : Bool := {
  defValue := true
  descr := "enable the `broadImport` linter"
}

/-- Gets the value of the `linter.broadImport` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.broadImport o

/-- The `broadImport` linter: this lints any `import Mathlib.Tactic` statement.

**Why is this bad?** This line imports the whole tactic folder: this is both unnecessarily broad
and can in fact create import cycles.
**How to fix this?** Minimize the import: only import the tactics you need.
`import Mathlib.Tactic.Common` is reasonable to import and will suffice.
-/
def broadImportLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    match stx.findStack? (fun _ ↦ true) (fun _ ↦ true) /- is_broad_import-/ with
    | _ => return -- TODO: implement

--initialize addLinter broadImportLinter

end Mathlib.Linter.Style.BroadImport
