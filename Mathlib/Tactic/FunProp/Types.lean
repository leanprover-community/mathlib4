/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Batteries.Data.RBMap.Basic

import Mathlib.Tactic.FunProp.FunctionData

import Batteries.Lean.HashSet

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

/-- Indicated origin of a function or a statement. -/
inductive Origin where
  /-- It is a constant defined in the environment. -/
  | decl (name : Name)
  /-- It is a free variable in the local context. -/
  | fvar (fvarId : FVarId)
  deriving Inhabited, BEq

/-- Name of the origin. -/
def Origin.name (origin : Origin) : Name :=
  match origin with
  | .decl name => name
  | .fvar id => id.name

/-- Get the expression specified by `origin`. -/
def Origin.getValue (origin : Origin) : MetaM Expr := do
  match origin with
  | .decl name => mkConstWithFreshMVarLevels name
  | .fvar id => pure (.fvar id)

/-- Pretty print `FunProp.Origin`. -/
def ppOrigin {m} [Monad m] [MonadEnv m] [MonadError m] : Origin → m MessageData
  | .decl n => return m!"{← mkConstWithLevelParams n}"
  | .fvar n => return mkFVar n

/-- Pretty print `FunProp.Origin`. Returns string unlike `ppOrigin`. -/
def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.name)

/-- Get origin of the head function. -/
def FunctionData.getFnOrigin (fData : FunctionData) : Origin :=
  match fData.fn with
  | .fvar id => .fvar id
  | .const name _ => .decl name
  | _ => .decl Name.anonymous

/-- Default names to be considered reducible by `fun_prop` -/
def defaultNamesToUnfold : Array Name :=
  #[`id, `Function.comp, `Function.HasUncurry.uncurry, `Function.uncurry]

/-- `fun_prop` configuration -/
structure Config where
  /-- Name to unfold -/
  constToUnfold : Batteries.RBSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  /-- Maximal number of transitions between function properties
  e.g. inferring differentiability from linearity -/
  maxDepth := 200
  /-- current depth -/
  depth := 0
  /-- Stack of used theorem, used to prevent trivial loops. -/
  thmStack : List Origin := []
  /-- Maximum number of steps `fun_prop` can take. -/
  maxSteps := 100000
deriving Inhabited

/-- `fun_prop` state -/
structure State where
  /-- Simp's cache is used as the `funProp` tactic is designed to be used inside of simp and utilize
  its cache -/
  cache        : Simp.Cache := {}
  /-- Count the number of steps and stop when maxSteps is reached. -/
  numSteps := 0
  /-- Log progress and failures messages that should be displayed to the user at the end. -/
  msgLog : List String := []

/-- Log used theorem -/
def Config.addThm (cfg : Config) (thmId : Origin) : Config :=
  {cfg with thmStack := thmId :: cfg.thmStack}

/-- Increase depth -/
def Config.increaseDepth (cfg : Config) : Config :=
  {cfg with depth := cfg.depth + 1}

/-- -/
abbrev FunPropM := ReaderT FunProp.Config $ StateT FunProp.State MetaM


/-- Result of `funProp`, it is a proof of function property `P f` -/
structure Result where
  /-- -/
  proof : Expr

/-- Check if previously used theorem was `thmOrigin`. -/
def previouslyUsedThm (thmOrigin : Origin) : FunPropM Bool := do
  match (← read).thmStack.head? with
  | .some thmOrigin' => return thmOrigin == thmOrigin'
  | _ => return false

/-- Puts the theorem to the stack of used theorems. -/
def withTheorem {α} (thmOrigin : Origin) (go : FunPropM α) : FunPropM α := do
  let cfg ← read
  if cfg.depth > cfg.maxDepth then
    throwError s!"fun_prop error, maximum depth({cfg.maxDepth}) reached!"
  withReader (fun cfg => cfg.addThm thmOrigin |>.increaseDepth) do go

/-- Default names to unfold -/
def defaultUnfoldPred : Name → Bool :=
  defaultNamesToUnfold.contains

/-- Get predicate on names indicating if theys shoulds be unfolded. -/
def unfoldNamePred : FunPropM (Name → Bool) := do
  let toUnfold := (← read).constToUnfold
  return fun n => toUnfold.contains n

/-- Increase heartbeat, throws error when `maxSteps` was reached -/
def increaseSteps : FunPropM Unit := do
  let numSteps := (← get).numSteps
  let maxSteps := (← read).maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})

/-- Log error message that will displayed to the user at the end. -/
def logError (msg : String) : FunPropM Unit := do
  modify fun s =>
    {s with msgLog := msg::s.msgLog}
