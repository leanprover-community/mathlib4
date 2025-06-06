/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Batteries.Tactic.Lint
import Mathlib.Tactic.DeclarationNames

/-!
# Linters for Mathlib

In this file we define additional linters for mathlib,
which concern the *behaviour* of the linted code, and not issues of code style or formatting.

Perhaps these should be moved to Batteries in the future.
-/

namespace Batteries.Tactic.Lint
open Lean Meta

/--
Linter that checks whether a structure should be in Prop.
-/
@[env_linter] def structureInType : Linter where
  noErrorsFound := "no structures that should be in Prop found."
  errorsFound := "FOUND STRUCTURES THAT SHOULD BE IN PROP."
  test declName := do
    unless isStructure (← getEnv) declName do return none
    -- remark: using `Lean.Meta.isProp` doesn't suffice here, because it doesn't (always?)
    -- recognize predicates as propositional.
    let isProp ← forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName))
      fun _ ty ↦ return ty == .sort .zero
    if isProp then return none
    let projs := (getStructureInfo? (← getEnv) declName).get!.fieldNames
    if projs.isEmpty then return none -- don't flag empty structures
    let allProofs ← projs.allM (do isProof <| ← mkConstWithLevelParams <| declName ++ ·)
    unless allProofs do return none
    return m!"all fields are propositional but the structure isn't."

/-- Linter that check that all `deprecated` tags come with `since` dates. -/
@[env_linter] def deprecatedNoSince : Linter where
  noErrorsFound := "no `deprecated` tags without `since` dates."
  errorsFound := "FOUND `deprecated` tags without `since` dates."
  test declName := do
    let some info := Lean.Linter.deprecatedAttr.getParam? (← getEnv) declName | return none
    match info.since? with
    | some _ => return none -- TODO: enforce `YYYY-MM-DD` format
    | none => return m!"`deprecated` attribute without `since` date"

end Batteries.Tactic.Lint

namespace Mathlib.Linter

/-!
#  `dupNamespace` linter

The `dupNamespace` linter produces a warning when a declaration contains the same namespace
at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.
-/

/--
The `dupNamespace` linter is set on by default.  Lean emits a warning on any declaration that
contains the same namespace at least twice consecutively.

For instance, `Nat.Nat.foo` and `One.two.two` trigger a warning, while `Nat.One.Nat` does not.

*Note.*
This linter will not detect duplication in namespaces of autogenerated declarations
(other than the one whose `declId` is present in the source declaration).
-/
register_option linter.dupNamespace : Bool := {
  defValue := true
  descr := "enable the duplicated namespace linter"
}

namespace DupNamespaceLinter

open Lean Parser Elab Command Meta Linter

@[inherit_doc linter.dupNamespace]
def dupNamespace : Linter where run := withSetOptionIn fun stx ↦ do
  if getLinterValue linter.dupNamespace (← getLinterOptions) then
    let mut aliases := #[]
    if let some exp := stx.find? (·.isOfKind `Lean.Parser.Command.export) then
      aliases ← getAliasSyntax exp
    for id in (← getNamesFrom (stx.getPos?.getD default)) ++ aliases do
      let declName := id.getId
      if declName.hasMacroScopes then continue
      let nm := declName.components
      let some (dup, _) := nm.zip (nm.tailD []) |>.find? fun (x, y) ↦ x == y
        | continue
      Linter.logLint linter.dupNamespace id
        m!"The namespace '{dup}' is duplicated in the declaration '{declName}'"

initialize addLinter dupNamespace

end Mathlib.Linter.DupNamespaceLinter
