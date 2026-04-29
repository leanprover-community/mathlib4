/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public meta import Lean.Elab.Command
public meta import Mathlib.Tactic.Linter.Header

/-!
# The `simpaUsingBy` linter

The `simpaUsingBy` linter emits a warning on `simpa ... using by ...`.
These are better written as `simp ...; ...`, which keeps the proof in tactic mode and avoids
hiding the main tactic behind a `using by` term.
-/

meta section

open Lean Elab Linter

namespace Mathlib.Linter.Style

/--
The "simpaUsingBy" linter emits a warning on `simpa ... using by ...`.
These are better written as `simp ...; ...`, which keeps the proof in tactic mode and avoids
hiding the main tactic behind a `using by` term.
-/
public register_option linter.style.simpaUsingBy : Bool := {
  defValue := false
  descr := "enable the simpaUsingBy linter"
}

namespace SimpaUsingBy

/-- Whether a piece of syntax is a `using by ...` argument in a `simpa`. -/
def isUsingByArg : Syntax → Bool
  | .node _ `null #[.atom _ "using", term] => term.isOfKind ``Lean.Parser.Term.byTactic
  | _ => false

/-- Whether a piece of syntax is `simpa ... using by ...`. -/
def isSimpaUsingBy : Syntax → Bool
  | .node _ ``Lean.Parser.Tactic.simpa args =>
      match args.back? with
      | some (.node _ ``Lean.Parser.Tactic.simpaArgsRest restArgs) =>
          restArgs.any isUsingByArg
      | _ => false
  | _ => false

/-- `getSimpaUsingBy stx` returns every occurrence of `simpa ... using by ...` in `stx`. -/
partial def getSimpaUsingBy : Syntax → Array Syntax
  | stx@(.node _ _ args) =>
      let children := args.flatMap getSimpaUsingBy
      if isSimpaUsingBy stx then
        children.push stx
      else
        children
  | _ => #[]

@[inherit_doc linter.style.simpaUsingBy]
def simpaUsingByLinter : Linter where run := withSetOptionIn fun stx => do
    unless getLinterValue linter.style.simpaUsingBy (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    for badSimpa in getSimpaUsingBy stx do
      Linter.logLint linter.style.simpaUsingBy badSimpa
        m!"Please replace `simpa [foo] using by <tactic>` with `simp [foo]; <tactic>`."

initialize addLinter simpaUsingByLinter

end SimpaUsingBy
end Mathlib.Linter.Style
