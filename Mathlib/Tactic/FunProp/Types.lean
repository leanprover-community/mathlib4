/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
public import Mathlib.Tactic.FunProp.FunctionData
public import Mathlib.Tactic.FunProp.Decl
public import Qq

/-!
## `funProp`

this file defines environment extension for `funProp`
-/

public meta section


namespace Mathlib
open Lean Meta
open Std (TreeSet)

namespace Meta.FunProp

initialize registerTraceClass `Meta.Tactic.fun_prop
initialize registerTraceClass `Meta.Tactic.fun_prop.attr
initialize registerTraceClass `Debug.Meta.Tactic.fun_prop


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
  #[`id, `Function.comp, `Function.const, `Function.HasUncurry.uncurry, `Function.uncurry]

/-- `fun_prop` configuration -/
structure Config where
  /-- Maximum number of transitions between function properties. For example inferring continuity
  from differentiability and then differentiability from smoothness (`ContDiff ℝ ∞`) requires
  `maxTransitionDepth = 2`. The default value of one expects that transition theorems are
  transitively closed e.g. there is a transition theorem that infers continuity directly from
  smoothness.

  Setting `maxTransitionDepth` to zero will disable all transition theorems. This can be very
  useful when `fun_prop` should fail quickly. For example when using `fun_prop` as discharger in
  `simp`.
  -/
  maxTransitionDepth := 1
  /-- Maximum number of steps `fun_prop` can take. -/
  maxSteps := 100000
deriving Inhabited, BEq

/-- `fun_prop` context -/
structure Context where
  /-- `fun_prop` config -/
  config : Config := {}
  /-- Name to unfold -/
  constToUnfold : TreeSet Name Name.quickCmp :=
    .ofArray defaultNamesToUnfold _
  /-- Custom discharger to satisfy theorem hypotheses. -/
  disch : Expr → MetaM (Option Expr) := fun _ => pure none
  /-- current transition depth -/
  transitionDepth := 0

/-- General theorem about a function property used for transition and morphism theorems -/
structure GeneralTheorem where
  /-- function property name -/
  funPropName : Name
  /-- theorem name -/
  thmName : Name
  /-- discrimination tree keys used to index this theorem -/
  keys : List (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry)
  /-- priority -/
  priority : Nat  := eval_prio default
  deriving Inhabited

/-- Structure holding transition or morphism theorems for `fun_prop` tactic. -/
structure GeneralTheorems where
  /-- Discrimination tree indexing theorems. -/
  theorems : RefinedDiscrTree GeneralTheorem := {}
  deriving Inhabited

/-- Goal of `fun_prop` like `Continuous (fun x => exp x + x)`

The need for this structure is because the goal can have metavariables/output parameters.

Without output parameters:
  `numOutParams` = 0
  `goal` is just something like `Continuous (fun x => exp x + x)`

With output parameters:
  `numOutParams` = 1
  `goal` each output parameter is abstracted into a binder like
    `fun f' => HasFDerivAt ℝ (fun x => expr x + x) f' x₀` -/
structure Goal where
  /-- Number of output parameters -/
  numOutParams : Nat
  /-- Goal expression with potential binders for ever output parameters. -/
  expr : Expr
  /-- Function property declaration -/
  decl : FunPropDecl
  /-- Main function in the fun_prop goal -/
  mainFun : Expr
deriving BEq, Hashable

/-- Return goal expression with fresh metavariables for every output parameters. -/
def Goal.mkFreshExpr (goal : Goal) : MetaM (Array Expr × Expr) := do
  let (xs, _, b) ← lambdaMetaTelescope goal.expr
  return (xs, b)

-- e.setArg funPropDecl.funArgId b
def Goal.updateMainFun (goal : Goal) (f : Expr) : MetaM Goal := do
  let expr ← lambdaTelescope goal.expr fun xs e =>
    mkLambdaFVars xs (e.setArg goal.decl.funArgId f)
  return { goal with
    expr
    mainFun := f }

/-- result of abstractAppArgsWithMVars -/
structure AbstractArgsMVarsResult where
  args : Array Expr
  expr : Expr
  deriving Inhabited, BEq


/-- Abstracts arguments containing metavariables in an application expression into lambda-bound
variables.

Given an expression `f a₁ a₂ ... aₙ` where some arguments contain metavariables, this function
will return:
  - `args`: subset of of `aᵢ` that contain metavariables
  - `expr`: `f` abstracted over all the arguments containing metavariables

**Example:**
```lean
Input:  (1 : Nat) + (2 + ?n)
Output: expr := fun a => 1 + a
        args := #[2 + ?n] -/
def abstractAppArgsWithMVars (e : Expr) : MetaM AbstractArgsMVarsResult := do
  if ¬e.hasExprMVar then
    return { args := #[], expr := e }

  let (fn, args) := e.withApp fun fn args => (fn, args)
  let some i := args.findIdx? fun arg => arg.hasExprMVar
    | throwError m!"unexpected metavariable in {e}"
  let fn := fn.beta args[0:i]
  let args := args[i:].toList
  go (← inferType fn) fn args #[] #[]
where
  go (type : Expr) (fn : Expr) (args : List Expr) (margs : Array Expr) (vars : Array Expr) :
    MetaM AbstractArgsMVarsResult :=
  match type, args with
  | .forallE n t b _, arg :: args => do
    if ¬arg.hasExprMVar ∧ (← isDefEq t (← inferType arg)) then
      go (b.instantiate1 arg) (fn.app arg) args margs vars
    else
      withLocalDeclD n t fun var =>
        go (b.instantiate1 var) (fn.app var) args (margs.push arg) (vars.push var)
  | _, _ => do
    return {
      args := vars
      expr := ← mkLambdaFVars vars fn
    }

def getFunPropGoal? (e : Expr) : MetaM (Option Goal) := do
  let e ← instantiateMVars e
  -- todo: correct implementation
  let some (decl, f) ← getFunProp? e | return none

  let r ← abstractAppArgsWithMVars e

  return some {
    numOutParams := r.args.size
    expr := r.expr
    decl
    mainFun := f
  }

set_option linter.style.docString.empty false in
/-- Result of `funProp`, it is a proof of function property `P f` -/
structure Result where
  /-- -/
  proof : Expr
  /-- Concrete values for output parameters -/
  outputs : Array Expr

/-- `fun_prop` state -/
structure State where
  /-- Simp's cache is used as the `fun_prop` tactic is designed to be used inside of simp and
  utilize its cache. It holds successful goals. -/
  cache : Std.HashMap Goal Result := {}
  /-- Cache storing failed goals such that they are not tried again. -/
  failureCache : ExprSet := {}
  /-- Count the number of steps and stop when maxSteps is reached. -/
  numSteps := 0
  /-- Log progress and failures messages that should be displayed to the user at the end. -/
  msgLog : List String := []
  /-- `RefinedDiscrTree` is lazy, so we store the partially evaluated tree. -/
  morTheorems : GeneralTheorems
  /-- `RefinedDiscrTree` is lazy, so we store the partially evaluated tree. -/
  transitionTheorems : GeneralTheorems

/-- Increase depth -/
def Context.increaseTransitionDepth (ctx : Context) : Context :=
  {ctx with transitionDepth := ctx.transitionDepth + 1}

/-- Monad to run `fun_prop` tactic in. -/
abbrev FunPropM := ReaderT FunProp.Context <| StateT FunProp.State MetaM

/-- Default names to unfold -/
def defaultUnfoldPred : Name → Bool :=
  defaultNamesToUnfold.contains

/-- Get predicate on names indicating whether they should be unfolded. -/
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

/-- Increase transition depth. Return `none` if maximum transition depth has been reached. -/
def withIncreasedTransitionDepth {α} (go : FunPropM (Option α)) : FunPropM (Option α) := do
  let maxDepth := (← read).config.maxTransitionDepth
  let newDepth := (← read).transitionDepth + 1
  if newDepth > maxDepth then
    trace[Meta.Tactic.fun_prop]
    "maximum transition depth ({maxDepth}) reached
    if you want `fun_prop` to continue then increase the maximum depth with \
    `fun_prop (maxTransitionDepth := {newDepth})`"
    return none
  else
    withReader (fun s => {s with transitionDepth := newDepth}) go

/-- Log error message that will displayed to the user at the end.

Messages are logged only when `transitionDepth = 0` i.e. when `fun_prop` is **not** trying to infer
function property like continuity from another property like differentiability.
The main reason is that if the user forgets to add a continuity theorem for function `foo` then
`fun_prop` should report that there is a continuity theorem for `foo` missing. If we would log
messages `transitionDepth > 0` then user will see messages saying that there is a missing theorem
for differentiability, smoothness, ... for `foo`. -/
def logError (msg : String) : FunPropM Unit := do
  if (← read).transitionDepth = 0 then
    modify fun s =>
      {s with msgLog :=
        if s.msgLog.contains msg then
          s.msgLog
        else
          msg::s.msgLog}

/-- Forward declaration of main `funProp` function -/
initialize funPropImplRef : IO.Ref (Expr → FunPropM (Option Expr)) ←
  .mkRef fun _ => return none

/-- Solve fun_prop goal like `Continuous f` or `Differentiable ℝ fun x : ℝ => exp x + x` -/
def funProp (goal : Expr) : FunPropM (Option Expr) := do
  let impl ← funPropImplRef.get
  impl goal

end Meta.FunProp

end Mathlib
