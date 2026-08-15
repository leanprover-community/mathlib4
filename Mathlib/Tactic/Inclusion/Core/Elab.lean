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

/-- Collect the array of enabled inclusion families and pass them into `config`. -/
def collectInclusionFamilies (config : InclusionConfig) (familyStxs : Array Syntax) :
    TacticM InclusionConfig := do
  if familyStxs.isEmpty then
    throwError "At least one inclusion family must be specified"
  let mut families := #[]
  for familyStx in familyStxs do
    let family := familyStx.getId
    unless families.contains family do
      unless (← getInclusionFamily? family).isSome do
        throwError "Unknown inclusion family '{family}'"
      families := families.push family
  return { config with families }

/-- Declare syntax category for specifying inclusion parameters. -/
declare_syntax_cat inclusionParam

/-- Syntax for specifying an inclusion parameter. -/
syntax ident " := " term : inclusionParam

/-- Collect the set of enabled inclusion parameters and their user set values and pass them into
`config`. -/
def collectInclusionParams (config : InclusionConfig) (paramStxs : Array Syntax) :
    TacticM InclusionConfig := do
  let mut config := config
  let params := inclusionParamExt.getState (← getEnv)
  for paramStx in paramStxs do
    let (name, valueStx) ← match paramStx with
      | `(inclusionParam| $name:ident := $value:term) => pure (name.getId, value)
      | _ => throwUnsupportedSyntax
    let some decl := params.find? name
      | throwError "Unknown inclusion parameter '{name}'"
    if config.paramSettings.contains name then
      throwError "Inclusion parameter '{name}' was specified more than once"
    let value ← elabTerm valueStx decl.type
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    config := { config with paramSettings := config.paramSettings.insert name value }
  return config

/-- Syntax for the `inclusion` tactic. -/
syntax (name := inclusionTacStx) "inclusion" optConfig " [" ident,* "]"
  (" (" inclusionParam,* ")")? : tactic

/-- `inclusion` tactic for proving "inclusion" propositions. -/
@[tactic inclusionTacStx]
def inclusionTac : Tactic
  | `(tactic| inclusion $cfg:optConfig [$families,*] $[($paramStxs,*)]?) => do
      let config ← elabInclusionConfig cfg
      let config ← collectInclusionFamilies config families.getElems
      let params := paramStxs.map (·.getElems) |>.getD #[]
      let config ← collectInclusionParams config params
      closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config
  | _ => throwUnsupportedSyntax

/-- Syntax for the `inclusion?` tactic. -/
syntax (name := inclusion?TacStx) "inclusion?" " [" ident,* "]"
  (" (" inclusionParam,* ")")? : tactic

/-- Tactic for quickly checking if the `inclusion` tactic will succeed. -/
@[tactic inclusion?TacStx]
def inclusion?Tac : Tactic
  | `(tactic| inclusion? [$families,*] $[($paramStxs,*)]?) => do
      let config : InclusionConfig := {}
      let config ← collectInclusionFamilies config families.getElems
      let params := paramStxs.map (·.getElems) |>.getD #[]
      let config ← collectInclusionParams config params
      withoutModifyingStateWithInfoAndMessages <| withMainContext do
        try
          discard <| inclusionCore (← getMainTarget) config
          logInfo "The inclusion check succeeded."
        catch err =>
          logInfo m!"The inclusion check failed:\n{err.toMessageData}"
  | _ => throwUnsupportedSyntax

end Inclusion
