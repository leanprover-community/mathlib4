/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Print
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Lemma

/-!
#  The "generic" linter

The "generic" linter takes as input a function
`unwanted : Syntax → Array Syntax` that returns the syntax nodes of an input syntax that
should be flagged.


Future extensions:
* Add `blackout? : Syntax → Bool` to prevent further inspection by the linter?
* Add `context? : InfoTree → Bool` for further effects combining `unwanted` and `blackout?` and
  possibly doing some further filtering?

See  #11890 for an example of how this may be extended.
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- The "generic" linter emits a warning on all syntax matching a given pattern. -/
register_option linter.generic : Bool := {
  defValue := true
  descr := "enable the generic linter"
}

namespace generic

/-- counts the total number of declarations implied by the one with identifier `id`. -/
def tal (id : TSyntax `ident) : CommandElabM (Name × Nat) := liftCoreM do
  let env ← getEnv
  let decl ← realizeGlobalConstNoOverloadWithInfo id <|> return ``Nat
  let (_, { visited, .. }) := CollectAxioms.collect decl |>.run (← getEnv) |>.run {}
  let mut truncate := env.header.moduleNames.map fun n => Name.fromComponents <| n.components.take 2
  let mut out := mkRBMap Name Nat Name.cmp
  for d in visited do
    if let some idx := env.getModuleIdxFor? d then
      let n := truncate[idx.toNat]!
      out := out.insert n (out.findD n 0 + 1)
  let mut total := 0
  for (_, n) in out do
    total := total + n
  return (decl, total)

/-- extracts the `declId` of a declaration -/
def getDeclId : Syntax → Option (TSyntax ``Lean.Parser.Command.declId)
  | `($_dm:declModifiers def $id:declId $_ds* : $_t $_dv:declVal) => id
  | `($_dm:declModifiers theorem $id:declId $_ds* : $_t $_dv:declVal) => id
  | `($_dm:declModifiers instance $_prio $id:declId $_ds* : $_t $_dv:declVal) => id
  | _ => none

end generic

end Mathlib.Linter

namespace Mathlib.Linter.generic

/-- Gets the value of the `linter.generic` option. -/
def getLinterHash (o : Options) : Bool := Linter.getLinterValue linter.generic o

/-- The main implementation of the generic syntax linter. -/
def genericSyntaxLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterHash (← getOptions) do
      return
    if (← MonadState.get).messages.hasErrors then
      return
    if let some nm := getDeclId stx then
      let nm := nm.raw[0]
      if nm.isOfKind `ident then
        logInfoAt nm m!"{← tal ⟨nm⟩}"

initialize addLinter genericSyntaxLinter
