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
    if stx.isOfKind ``Lean.Parser.Command.variable then
      let sc ← getScope
      let varDecls := sc.varDecls
      let mut implied := #[]
      let s ← get
      for d in varDecls do
        if d.raw.isOfKind ``Lean.Parser.Term.instBinder then
          withScope (fun s => { s with varDecls := varDecls.erase d }) <|
            elabCommand (← `(command| #synth $(⟨d.raw[2]⟩)))
          if (← get).messages.hasErrors then set s else implied := implied.push d
      set s
      for d in implied do
        Linter.logLint linter.dependentTypeclass d m!"Typeclass '{d}' is implied"

initialize addLinter dependentTypeclassLinter

end DependentTypeclass

end Mathlib.Linter
