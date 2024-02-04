/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types

import Std.Lean.HashSet


/-!
## `funProp`

this file defines enviroment extension for `funProp`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


initialize registerTraceClass `Meta.Tactic.fun_prop.attr
initialize registerTraceClass `Meta.Tactic.fun_prop
initialize registerTraceClass `Meta.Tactic.fun_prop.step
initialize registerTraceClass `Meta.Tactic.fun_prop.unify
initialize registerTraceClass `Meta.Tactic.fun_prop.discharge
initialize registerTraceClass `Meta.Tactic.fun_prop.apply
initialize registerTraceClass `Meta.Tactic.fun_prop.unfold
initialize registerTraceClass `Meta.Tactic.fun_prop.cache


/-- -/
structure Config where
  /-- Name to unfold -/
  constToUnfold : HashSet Name := .ofArray #[``id, ``Function.comp, ``Function.HasUncurry.uncurry]
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  /-- Maximal number of transitions between function properties
  e.g. infering differentiability from linearity -/
  maxTransitionDepth := 20
  /-- Stack of used theorem, used to prevent trivial loops. -/
  thmStack    : List Origin := []

/-- -/
structure State where
  /-- Simp's cache is used as the `funProp` tactic is designed to be used inside of simp and utilize
  its cache -/
  cache        : Simp.Cache := {}
  /-- The number of used transition theorems. -/
  transitionDepth := 0

/-- Log used theorem -/
def Config.addThm (cfg : Config) (thmId : Origin) :
    Config :=
  {cfg with thmStack := thmId :: cfg.thmStack}

/-- -/
abbrev FunPropM := ReaderT FunProp.Config $ StateT FunProp.State MetaM


/-- Result of `funProp`, it is a proof of function property `P f` -/
structure Result where
  /-- -/
  proof : Expr

/-- Get the name of previously used theorem. -/
def getLastUsedTheoremName : FunPropM (Option Name) := do
  match (← read).thmStack.head? with
  | .some (.decl n) => return n
  | _ => return none
