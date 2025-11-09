/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Michael Rothgang
-/
import Batteries.Tactic.Lint
import Mathlib.Lean.Expr.Basic

/-!
# Linters for unused assumptions in a type

This file defines a collection of similar linters, which check for declarations assuming a
hypothesis of the form `[Type p]` which contains an assumption about `p` that is not used:
this includes `Decidable p`, `Encodable p`, `Inhabited p` and others.
Usually, the code can be restructured to avoid these assumptions, making the statements in question
more general.
-/

namespace Batteries.Tactic.Lint
open Lean Meta

/-- Check if a given declaration assumes some hypothesis `[Type p]`, but doesn't use this
assumption in the type. `typesToAvoid` the list of such types.
This is the main logic underlying the linters below. -/
def checkUnusedAssumptionInType (declInfo : ConstantInfo) (typesToAvoid : Array Name) :
    MetaM (Option MessageData) := do
  -- We omit inductive types and their constructors, to reduce false positives.
  -- We also omit partial declarations (via the `opaque` definitions they generate):
  -- these are less useful for theorem proving, hence the linter is less useful there.
  if declInfo matches .inductInfo .. | .ctorInfo .. | .opaqueInfo .. then return none
  let type := declInfo.type
  -- Early return: none of the constants to avoid appear.
  unless type.containsConst typesToAvoid.contains do
    return none
  -- Compute an array of pairs (argument index, error message) for each superfluous argument:
  -- the first component is the index of the superfluous argument, the second component
  -- contains details about the error.
  let mut impossibleArgs ← forallTelescopeReducing type fun args ty ↦ do
    let argTys ← args.mapM inferType
    let ty ← ty.eraseProofs
    return ← (args.zip argTys.zipIdx).filterMapM fun (arg, t, i) ↦ do
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
    else if Name.isPrefixOf `Decidable declName then return none
    let names := #[`Decidable, `DecidableEq, `DecidablePred]
    return ← checkUnusedAssumptionInType (← getConstInfo declName) names

/--
Linter that checks for theorems that assume `[Inhabited p]`
but don't use this assumption in the type.
-/
@[env_linter] def inhabitedNonempty : Linter where
  noErrorsFound := "No uses of `Inhabited` arguments should be replaced"
  errorsFound := "USES OF `Inhabited` SHOULD BE REPLACED WITH `Nonempty` (OR REMOVED)."
  test declName := do
    if (← isAutoDecl declName) then return none
    return ← checkUnusedAssumptionInType (← getConstInfo declName) #[`Inhabited]

/--
Linter that checks for theorems that assume `[Fintype p]`,
but don't use this assumption in the type.
(Instead, `Finite p` can suffice, or the assumption can be fully removed.)
-/
@[env_linter] def finiteFintype : Linter where
  noErrorsFound := "No uses of `Fintype` arguments should be replaced"
  errorsFound := "USES OF `Fintype` SHOULD BE REPLACED WITH `Finite` (OR REMOVED)."
  test declName := do
    if (← isAutoDecl declName) then return none
    return ← checkUnusedAssumptionInType (← getConstInfo declName) #[`Fintype]

/--
Linter that checks for theorems that assume `[Encodable p]`,
but don't use this assumption in the type.
(Instead, `Countable p` can suffice, or the assumption can be fully removed.)
-/
@[env_linter] def encodableCountable : Linter where
  noErrorsFound := "No uses of `Encodable` arguments should be replaced"
  errorsFound := "USES OF `Encodable` SHOULD BE REPLACED WITH `Countable` (OR REMOVED)."
  test declName := do
    if (← isAutoDecl declName) then return none
    else if Name.isPrefixOf `Encodable declName then return none
    return ← checkUnusedAssumptionInType (← getConstInfo declName) #[`Encodable]

end Batteries.Tactic.Lint
