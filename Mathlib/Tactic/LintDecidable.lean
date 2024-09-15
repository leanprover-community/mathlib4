/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Batteries.Tactic.Lint
import Mathlib.Lean.Expr.Basic

/-!
# Linter for `Decidable`/`Encodable`/`Inhabited`
-/

namespace Std.Tactic.Lint
open Lean Meta

/-- Check if a given declaration assumes some hypothesis `[Type p]`, but doesn't use this
assumption in the type. `typesToAvoid` the list of such types.
This is the main logic underlying the linters below. -/
def checkUnusedAssumptionInType (declInfo : ConstantInfo) (typesToAvoid : Array Name) :
    MetaM (Option MessageData) := do
  let type := declInfo.type
  -- Compute an array of pairs (argument index, error message) for each superfluous argument:
  -- the first component is the index of the superfluous argument, the second component
  -- contains details about the error.
  let mut impossibleArgs ← forallTelescopeReducing type fun args ty ↦ do
    let argTys ← args.mapM inferType
    let ty ← ty.eraseProofs
    return ← (args.zip argTys.zipWithIndex).filterMapM fun (arg, t, i) ↦ do
      unless typesToAvoid.any t.cleanupAnnotations.getForallBody.isAppOf do return none
      let fv := arg.fvarId!
      if ty.containsFVar fv then return none
      if argTys[i+1:].any (·.containsFVar fv) then return none
      return some (i, (← addMessageContextFull m!"argument {i+1} {arg} : {t}"))
  if !(← isProp type) then
    if let some e := declInfo.value? then
      impossibleArgs ← lambdaTelescope e fun args e ↦ do
        let e ← e.eraseProofs
        return impossibleArgs.filter fun (k, _) ↦
          k < args.size && !e.containsFVar args[k]!.fvarId!
  if impossibleArgs.isEmpty then return none
  return some <| .joinSep (impossibleArgs.toList.map Prod.snd) ", "

/--
Linter that checks for theorems that assume `[Decidable p]`
but don't use this assumption in the type.
-/
@[env_linter] def decidableClassical : Linter where
  noErrorsFound := "No uses of `Decidable` arguments should be replaced with `classical`"
  errorsFound := "USES OF `Decidable` SHOULD BE REPLACED WITH `classical` IN THE PROOF."
  test declName := do
    if (← isAutoDecl declName) then return none
    let names :=
      if Name.isPrefixOf `Decidable declName then #[`Fintype, `Encodable]
      else #[`Decidable, `DecidableEq, `DecidablePred, `Inhabited, `Fintype, `Encodable]
    return ← checkUnusedAssumptionInType (← getConstInfo declName) names

end Std.Tactic.Lint
