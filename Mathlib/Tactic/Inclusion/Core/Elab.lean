/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public meta import Mathlib.Tactic.Inclusion.Core.Core
meta import Lean.Elab.ConfigEval
meta import Mathlib.Tactic.Linter.UnusedTacticExtension

/-!
# Elaboration of the `inclusion` tactic

This file defines the syntax and elaborator for the `inclusion` tactic.
-/

public meta section

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

namespace Inclusion

/-- Configuration elaborator for `inclusion`; families and parameter values use custom syntax. -/
declare_config_elab elabInclusionConfig InclusionConfig where
  omit paramSettings, families

/-- Syntax for assigning an inclusion parameter. -/
declare_syntax_cat inclusionParam

syntax ident " := " term : inclusionParam

/-- Elaborate and validate the list of inclusion families enabled by a tactic invocation. -/
def elabInclusionFamilies (config : InclusionConfig) (familyStxs : Array Syntax) :
    TacticM InclusionConfig := do
  if familyStxs.isEmpty then
    throwError "At least one inclusion family must be specified"
  let mut families := #[]
  for familyStx in familyStxs do
    let family := familyStx.getId
    unless (← getInclusionFamily? family).isSome do
      throwError "Unknown inclusion family '{family}'"
    if families.contains family then
      throwError "Inclusion family '{family}' was enabled more than once"
    families := families.push family
  return { config with families }

/-- Elaborate an inclusion-parameter value against its registered type. -/
private def elabParamTerm (stx : Syntax) (expectedType : Expr) : TacticM Expr := do
  let value ← elabTerm stx expectedType
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars value

/-- Elaborate inclusion parameters. -/
def elabInclusionParams (config : InclusionConfig) (paramStxs : Array Syntax) :
    TacticM InclusionConfig := do
  let mut config := config
  let registeredParams := inclusionParamExt.getState (← getEnv)
  for paramStx in paramStxs do
    let (name, valueStx) ← match paramStx with
      | `(inclusionParam| $name:ident := $value:term) =>
        pure (name.getId, value)
      | _ => throwUnsupportedSyntax
    let some decl := registeredParams.find? name
      | throwError "Unknown inclusion parameter '{name}'"
    let value ← elabParamTerm valueStx decl.type
    if config.paramSettings.contains name then
      throwError "Inclusion parameter '{name}' was specified more than once"
    config := { config with paramSettings := config.paramSettings.insert name value }
  return config

syntax (name := inclusionTacStx) "inclusion" optConfig " [" ident,* "]"
  (" (" inclusionParam,* ")")? : tactic

/-- `inclusion` tactic for proving "inclusion" propositions. -/
@[tactic inclusionTacStx]
def inclusionTac : Tactic
  | `(tactic| inclusion $cfg:optConfig [$families,*] $[($paramStxs,*)]?) => do
      let config ← elabInclusionConfig cfg
      let config ← elabInclusionFamilies config families.getElems
      let params := paramStxs.map (·.getElems) |>.getD #[]
      let config ← elabInclusionParams config params
      closeMainGoalUsing `inclusion fun goal _ => inclusionCore goal config
  | _ => throwUnsupportedSyntax

syntax (name := inclusion?TacStx) "inclusion?" optConfig " [" ident,* "]"
  (" (" inclusionParam,* ")")? : tactic

/-- Tactic for quickly checking if the `inclusion` tactic will succeed. -/
@[tactic inclusion?TacStx]
def inclusion?Tac : Tactic
  | `(tactic| inclusion? $cfg:optConfig [$families,*] $[($paramStxs,*)]?) => do
      let config ← elabInclusionConfig cfg
      let config ← elabInclusionFamilies config families.getElems
      let params := paramStxs.map (·.getElems) |>.getD #[]
      let config ← elabInclusionParams config params
      withoutModifyingStateWithInfoAndMessages <| withMainContext do
        try
          discard <| inclusionCore (← getMainTarget)
            { config with kernel := false, native := false }
          logInfo "The inclusion check succeeded."
        catch err =>
          logInfo m!"The inclusion check failed:\n{err.toMessageData}"
  | _ => throwUnsupportedSyntax

initialize
  Mathlib.Linter.UnusedTactic.allowedRef.modify (·.insert `Inclusion.inclusion?TacStx)

end Inclusion
