/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Std.Data.RBMap.Basic

import Mathlib.Tactic.FunProp.FunctionData

import Std.Lean.HashSet

/-!
## `funProp`

this file defines environment extension for `funProp`
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

inductive Origin where
  | decl (name : Name)
  | fvar (fvarId : FVarId)
  deriving Inhabited, BEq

def Origin.name (origin : Origin) : Name :=
  match origin with
  | .decl name => name
  | .fvar id => id.name

def Origin.getValue (origin : Origin) : MetaM Expr := do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)

def FunctionData.getFnOrigin (fData : FunctionData) : Origin :=
  match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

/-- -/
structure Config where
  /-- Name to unfold -/
  constToUnfold : Std.RBSet Name Name.quickCmp := .ofArray #[`id, `Function.comp, `Function.HasUncurry.uncurry] _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  /-- Maximal number of transitions between function properties
  e.g. inferring differentiability from linearity -/
  maxTransitionDepth := 20
  /-- Stack of used theorem, used to prevent trivial loops. -/
  thmStack    : List Origin := []
  /-- Maximum number of steps `fun_prop` can take. -/
  maxSteps := 100000
deriving Inhabited

/-- -/
structure State where
  /-- Simp's cache is used as the `funProp` tactic is designed to be used inside of simp and utilize
  its cache -/
  cache        : Simp.Cache := {}
  /-- The number of used transition theorems. -/
  transitionDepth := 0
  /-- Count the number of steps and stop when maxSteps is reached. -/
  numSteps := 0

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

def defaultUnfoldPred : Name → Bool :=
  #[`id,`Function.comp,`Function.HasUncurry.uncurry,`Function.uncurry].contains

def unfoldNamePred : FunPropM (Name → Bool) := do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n

/-- Increase heartbeat, throws error when maxHeartbeat was reached -/
def increaseSteps : FunPropM Unit := do
  let numSteps := (← get).numSteps
  if numSteps > (← read).maxSteps then
     throwError "fun_prop failed, maximum number of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})
