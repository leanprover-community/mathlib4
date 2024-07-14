/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean

/-!
#  The "dependentTypeclass" linter

The "dependentTypeclass" linter emits a warning when there is a dependency among typeclass
assumptions.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "dependentTypeclass" linter emits a warning when there is a dependency among typeclass
assumptions.
 -/
register_option linter.dependentTypeclass : Bool := {
  defValue := true
  descr := "enable the dependentTypeclass linter"
}

namespace DependentTypeclass

/-- Gets the value of the `linter.dependentTypeclass` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.dependentTypeclass o

@[inherit_doc Mathlib.Linter.linter.dependentTypeclass]
def dependentTypeclassLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    -- we first find `variable`s that could be inside an `in`
    if let some stx := stx.find? (·.isOfKind ``Lean.Parser.Command.variable) then
      -- and then we extract the actual "variables" in `variable <vars*>`
      match stx with
        | `(variable $vars*) =>
          let sc ← getScope
          -- we add the "current" variables to the ones in scope, since otherwise the linter
          -- would "miss", as they are already outside of scope when the linter runs
          let varDecls := sc.varDecls ++ vars
          let insts := varDecls.filter (·.raw.isOfKind ``Lean.Parser.Term.instBinder)
          if insts.size ≤ 1 then return else
          let mut implied := #[]
          let s ← get
          for d in insts do
            -- we remove "all" `d`s, to deal better with the variable update
            -- `variable (α : Type) [Add α] variable {α} [Add α]`
            let noDvar := varDecls.filter (· != d)
            withScope (fun s => { s with varDecls := noDvar }) <|
              elabCommand (← `(command| #synth $(⟨d.raw[2]⟩)))
            if (← get).messages.hasErrors then
              set s
            else implied := implied.push (d, insts.filter (· != d))
          set s
          for (d, ctx) in implied do
            Linter.logLint linter.dependentTypeclass d m!"Typeclass '{d}' is implied by {ctx}"
        | _=> return
initialize addLinter dependentTypeclassLinter

end DependentTypeclass

end Mathlib.Linter
