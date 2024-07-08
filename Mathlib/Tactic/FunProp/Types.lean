/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.Tactic.FunProp.FunctionData

/-!
## `funProp`

this file defines environment extension for `funProp`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FunProp


initialize registerTraceClass `Meta.Tactic.fun_prop
initialize registerTraceClass `Meta.Tactic.fun_prop.attr
initialize registerTraceClass `Meta.Tactic.fun_prop.cache
initialize registerTraceClass `Meta.Tactic.fun_prop.errors
initialize registerTraceClass `Meta.Tactic.fun_prop.step

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

/-- Error logging mode for `fun_prop`. Main mode is used for messages that should be directly
displayed to the user and secondary mode is for messages that are displayed by setting option
`Meta.Tactic.fun_prop.errors` to true. -/
inductive LoggingMode where
  /-- Main error logging mode, these messages will be diplayed to the user be default. -/
  | main
  /-- Secondary error logging mode, these messages will be diplayed to the user by setting option
  `Meta.Tactic.fun_prop.errors` to true . -/
  | secondary

/-- Default names to be considered reducible by `fun_prop` -/
def defaultNamesToUnfold : Array Name :=
  #[`id, `Function.comp, `Function.HasUncurry.uncurry, `Function.uncurry]

/-- `fun_prop` configuration -/
structure Config where
  /-- Maximal number of transitions between function properties
  e.g. inferring differentiability from linearity -/
  maxDepth := 200
  /-- Maximum number of steps `fun_prop` can take. -/
  maxSteps := 100000
  /-- Use transition theorem. -/
  useTransThms := true
deriving Inhabited

/-- `fun_prop` context -/
structure Context where
  /-- fun_prop config -/
  config : Config := {}
  /-- Name to unfold -/
  constToUnfold : Batteries.RBSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure .none
  /-- current depth -/
  depth := 0
  /-- Stack of used theorem, used to prevent trivial loops. -/
  thmStack : List Origin := []
  /-- Logging mode, determines whether logged messages will be diplayes to the user immediately or
  on request by setting `Meta.Tactic.fun_prop.errors` to true. -/
  loggingMode : LoggingMode := .main

/-- `fun_prop` state -/
structure State where
  /-- Simp's cache is used as the `fun_prop` tactic is designed to be used inside of simp and
  utilize its cache -/
  cache        : Simp.Cache := {}
  /-- Count the number of steps and stop when maxSteps is reached. -/
  numSteps := 0
  /-- Log progress and failures messages that should be displayed to the user at the end. -/
  mainMsgLog : List String := []
  /-- Log progress and failures messages that should be displayed to the user at the end when
  the option `Meta.Tactic.fun_prop.errors` is set to true. -/
  secondaryMsgLog : List String := []

/-- Log used theorem -/
def Context.addThm (ctx : Context) (thmId : Origin) : Context :=
  {ctx with thmStack := thmId :: ctx.thmStack}

/-- Increase depth -/
def Context.increaseDepth (ctx : Context) : Context :=
  {ctx with depth := ctx.depth + 1}

/-- Monad to run `fun_prop` tactic in. -/
abbrev FunPropM := ReaderT FunProp.Context $ StateT FunProp.State MetaM

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
  let ctx ← read
  if ctx.depth > ctx.config.maxDepth then
    throwError s!"fun_prop error, maximum depth({ctx.config.maxDepth}) reached!"
  withReader (fun ctx => ctx.addThm thmOrigin |>.increaseDepth) do go

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
  let maxSteps := (← read).config.maxSteps
  if numSteps > maxSteps then
     throwError s!"fun_prop failed, maximum number({maxSteps}) of steps exceeded"
  modify (fun s => {s with numSteps := s.numSteps + 1})

/-- Run `fun_prop` but log all error messages as secondary. -/
def withSecondaryLoggingMode {α} (x : FunPropM α) : FunPropM α := do
  withReader (fun ctx => { ctx with loggingMode := .secondary })
    x

/-- Log error message that will displayed to the user at the end. -/
def logError (msg : String) : FunPropM Unit := do
  match (← read).loggingMode with
  | .main =>
    modify fun s =>
      {s with mainMsgLog := msg::s.mainMsgLog}
  | .secondary =>
    modify fun s =>
      {s with secondaryMsgLog := msg::s.secondaryMsgLog}
