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

/--
Linter that checks for theorems that assume `[Decidable p]`
but don't use this assumption in the type.
-/
@[std_linter] def decidableClassical : Linter where
  noErrorsFound := "No uses of `Decidable` arguments should be replaced with `classical`"
  errorsFound := "USES OF `Decidable` SHOULD BE REPLACED WITH `classical` IN THE PROOF."
  test declName := do
    if (← isAutoDecl declName) then return none
    let info ← getConstInfo declName
    let type := info.type
    let names :=
      if Name.isPrefixOf `Decidable declName then #[`Fintype, `Encodable]
      else if Name.isPrefixOf `Fintype declName
        then #[`Decidable, `DecidableEq, `DecidablePred, `Encodable]
        else if Name.isPrefixOf `Encodable declName
        then #[`Decidable, `DecidableEq, `DecidablePred, `Fintype]
        else #[`Decidable, `DecidableEq, `DecidablePred, `Fintype, `Encodable]
    let mut impossibleArgs ← forallTelescopeReducing type fun args ty => do
      let argTys ← args.mapM inferType
      let ty ← ty.eraseProofs
      return ← (args.zip argTys.zipWithIndex).filterMapM fun (arg, t, i) => do
        unless names.any t.cleanupAnnotations.getForallBody.isAppOf do return none
        let fv := arg.fvarId!
        if ty.containsFVar fv then return none
        if argTys[i+1:].any (·.containsFVar fv) then return none
        return some (i, (← addMessageContextFull m!"argument {i+1} {arg} : {t}"))
    if !(← isProp type) then
      if let some e := info.value? then
        impossibleArgs ← lambdaTelescope e fun args e => do
          let e ← e.eraseProofs
          return impossibleArgs.filter fun (k, _) => !e.containsFVar args[k]!.fvarId!
    if impossibleArgs.isEmpty then return none
    return some <| .joinSep (impossibleArgs.toList.map Prod.snd) ", "
