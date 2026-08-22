/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core
meta import Lean.Elab.ConfigEval

/-!
# Elaboration of the `inclusion` tactic

This file defines the syntax and elaborator for the `inclusion` tactic.
-/

public meta section

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

/-- Declare elaborator for the configuration `InclusionConfig` of the `inclusion` tactic. -/
declare_config_elab elabInclusionConfig InclusionConfig where
  omit paramSettings, families

/-- Syntax for specifying an inclusion family or parameter. -/
syntax inclusionArg := ident (" := " term)?

/-- Collect the enabled inclusion families and user-set parameter values and pass them into
`config`. -/
def collectInclusionArgs (config : InclusionConfig) (argStxs : Array Syntax) :
    TacticM InclusionConfig := do
  let mut config := config
  let params := inclusionParamExt.getState (← getEnv)
  for argStx in argStxs do
    match argStx with
    | `(inclusionArg| $familyStx:ident) =>
      let family := familyStx.getId.eraseMacroScopes
      unless config.families.contains family do
        unless (← getInclusionFamily? family).isSome do
          throwError "Unknown inclusion family `{family}`"
        config := { config with families := config.families.push family }
    | `(inclusionArg| $nameStx:ident := $valueStx:term) =>
      let name := nameStx.getId
      let some decl := params.find? name
        | throwError "Unknown inclusion parameter `{name}`"
      if config.paramSettings.contains name then
        throwError "Inclusion parameter `{name}` was specified more than once"
      let value ← elabTerm valueStx decl.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      config := { config with paramSettings := config.paramSettings.insert name value }
    | _ => throwUnsupportedSyntax
  if config.families.isEmpty then
    throwError "At least one inclusion family must be specified"
  return config

/-- `inclusion` tactic for proving "inclusion" propositions. -/
syntax (name := inclusionTacStx) "inclusion" optConfig " [" inclusionArg,* "]" : tactic

/-- Elaborator for the `inclusion` tactic. -/
@[tactic inclusionTacStx]
def inclusionTac : Tactic
  | `(tactic| inclusion $cfg:optConfig [$args,*]) => do
      let config ← elabInclusionConfig cfg
      let config ← collectInclusionArgs config args.getElems
      closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config
  | _ => throwUnsupportedSyntax

/-- Tactic for quickly checking if the `inclusion` tactic will succeed. -/
syntax (name := inclusion?TacStx) "inclusion?" " [" inclusionArg,* "]" : tactic

/-- Elaborator for the `inclusion?` tactic. -/
@[tactic inclusion?TacStx]
def inclusion?Tac : Tactic
  | `(tactic| inclusion? [$args,*]) => do
      let config : InclusionConfig := {}
      let config ← collectInclusionArgs config args.getElems
      withoutModifyingStateWithInfoAndMessages <| withMainContext do
        try
          discard <| inclusionCore (← getMainTarget) config
          logInfo "The inclusion check succeeded."
        catch err =>
          logInfo m!"The inclusion check failed:\n{err.toMessageData}"
  | _ => throwUnsupportedSyntax

end Inclusion
