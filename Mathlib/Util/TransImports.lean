/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Init

/-! # The `#trans_imports` command

`#trans_imports` reports how many transitive imports the current module has.
The command takes an optional string input: `#trans_imports str` also shows the transitively
imported modules whose name begins with `str`.
-/

public meta section

/--
`#trans_imports` reports how many transitive imports the current module has.
The command takes an optional string input: `#trans_imports str` also shows the transitively
imported modules whose name begins with `str`.

Mostly for the sake of tests, the command also takes an optional `at_most x` input:
if the number of imports does not exceed `x`, then the message involves `x`, rather than the
actual, possibly varying, number of imports.
-/
syntax (name := transImportsStx) "#trans_imports" (ppSpace str)? (&" at_most " num)? : command

open Lean in
@[inherit_doc transImportsStx]
elab_rules : command
| `(command| #trans_imports $(stx)? $[at_most $le:num]?) => do
  let imports := (← getEnv).allImportedModuleNames
  let currMod := if let mod@(.str _ _) := ← getMainModule then m!"'{mod}' has " else ""
  let rest := match stx with
      | none => m!""
      | some str =>
        let imps := imports.filterMap fun (i : Name) =>
          if i.toString.startsWith str.getString then some i else none
        m!"\n\n{imps.size} starting with {str}:\n{imps.qsort (·.toString < ·.toString)}"
  match le with
    | none => logInfo m!"{currMod}{imports.size} transitive imports{rest}"
    | some bd =>
      if imports.size ≤ bd.getNat then
        logInfo m!"{currMod}at most {bd} transitive imports{rest}"
      else
        logWarningAt bd
          m!"{currMod}{imports.size} transitive imports, exceeding the expected bound of {bd}{rest}"
