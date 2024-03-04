/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Std.Tactic.Lint
import Mathlib.Lean.Expr.Basic


/-!
# Linters for Mathlib

In this file we define additional linters for mathlib.

Perhaps these should be moved to Std in the future.
-/

namespace Std.Tactic.Lint
open Lean Meta

/--
Linter that checks whether a structure should be in Prop.
-/
@[std_linter] def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    -- remark: using `Lean.Meta.isProp` doesn't suffice here, because it doesn't (always?)
    -- recognize predicates as propositional.
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty => return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none -- don't flag empty structures
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."

end Std.Tactic.Lint

/-!
#  `dupNamespace` linter

The `dupNamespace` linter produces a warning when a declaration contains the same namespace
at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.
-/

namespace Mathlib.Linter

/--
The `dupNamespace` linter is set on by default.  Lean emits a warning on any declaration that
contains the same namespace at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.
-/
register_option linter.dupNamespace : Bool := {
  defValue := true
  descr := "enable the duplicated namespace linter"
}

namespace DupNamespaceLinter

open Lean Elab

/-- Gets the value of the `linter.dupNamespace` option. -/
def getLinterDupNamespace (o : Options) : Bool := Linter.getLinterValue linter.dupNamespace o

open Lean.Parser.Command in
partial
def getIds : Syntax → Array Syntax
  | stx@(.node _ _ args) => ((args.map getIds).foldl (· ++ ·) #[stx]).filter (·.getKind == ``declId)
  | _ => default

def dupNamespace : Linter where run := withSetOptionIn fun stx => do
  if getLinterDupNamespace (← getOptions) then
    match (getIds stx) with
      | #[id] =>
        let declName ← resolveGlobalConstNoOverload id[0]
        unless (← declName.isBlackListed) do
          let nm := declName.components
          let some (dup, _) := nm.zip nm.tail! |>.find? fun (x, y) => x == y
            | return
          logWarningAt id m!"The namespace '{dup}' is duplicated in the '{id}'\n\
            [linter.dupNamespace]"
      | _ => return

initialize addLinter dupNamespace
