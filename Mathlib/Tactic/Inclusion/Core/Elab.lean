/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core

/-!
# Elaboration of the `inclusion` tactic

This file defines the syntax and elaborator for the `inclusion` tactic.
-/

public meta section

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

declare_config_elab elabInclusionConfig InclusionConfig where
  omit paramSettings, families

/-- Families and parameters for the `inclusion` tactic -/
syntax inclusionArg := ident (" := " term)?

/-- Collect the enabled inclusion families and user-set parameter values. -/
def collectInclusionArgs (argStxs : Array Syntax) : TacticM InclusionConfig := do
  let mut paramSettings : NameMap Expr := {}
  let mut families := #[]
  let params := inclusionParamExt.getState (← getEnv)
  for argStx in argStxs do
    match argStx with
    | `(inclusionArg| $familyStx:ident) =>
      let family := familyStx.getId.eraseMacroScopes
      unless families.contains family do
        unless (← getInclusionFamily? family).isSome do
          throwError "Unknown inclusion family `{family}`"
        families := families.push family
    | `(inclusionArg| $nameStx:ident := $valueStx:term) =>
      let name := nameStx.getId
      let some decl := params.find? name
        | throwError "Unknown inclusion parameter `{name}`"
      if paramSettings.contains name then
        throwError "Inclusion parameter `{name}` was specified more than once"
      let value ← elabTerm valueStx decl.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      paramSettings := paramSettings.insert name value
    | _ => throwUnsupportedSyntax
  if families.isEmpty then
    throwError "At least one inclusion family must be specified"
  return { paramSettings, families }

/-- `inclusion` tactic for proving "inclusion" propositions. -/
elab (name := inclusion) "inclusion" cfg:optConfig " [" args:inclusionArg,* "]" : tactic => do
  let options ← elabInclusionConfig cfg
  let config ← collectInclusionArgs args.getElems
  let config := { config with kernel := options.kernel, native := options.native }
  closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config

/-- Tactic for quickly checking if the `inclusion` tactic will succeed. -/
elab (name := inclusion?) "inclusion?" " [" args:inclusionArg,* "]" : tactic => do
  let config ← collectInclusionArgs args.getElems
  withoutModifyingStateWithInfoAndMessages <| withMainContext do
    try
      discard <| inclusionCore (← getMainTarget) config
      logInfo "The inclusion check succeeded."
    catch err =>
      logError m!"The inclusion check failed:\n{err.toMessageData}"

end Inclusion
