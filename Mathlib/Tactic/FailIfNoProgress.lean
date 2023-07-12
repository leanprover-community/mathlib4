/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean
import Std

/-!
# Fail if no progress

This implements the `fail_if_no_progress` tactic, which fails if no actual progress is made by the
following tactic sequence.

"Actual progress" means that either the number of goals has changed, that the
number or presence of expressions in the context has changed, or that the type of some expression
in the context or the type of the goal is no longer definitionally equal to what it used to be at
reducible transparency.

This means that, for example, `1 - 1` changing to `0` does not count as actual progress, since
```lean
example : (1 - 1 = 0) := by with_reducible rfl
```

This tactic is useful in situations where we want to stop iterating some tactics if they're not
having any  effect, e.g. `repeat (fail_if_no_progress simp <;> ring_nf)`.






-/





namespace Mathlib.Tactic

open Lean Meta Elab Tactic Parser.Tactic

/-- Specifies which type of equality check to use. Either `.beq` or `.defEq`. -/
inductive EqKind where | beq | defEq
deriving Repr, Inhabited

/-- Returns `true` if its argument is `.beq` and `false` if `.defEq`. -/
def EqKind.isBEq : EqKind → Bool
  | .beq   => true
  | .defEq => false

/-- Config data for comparing expressions. -/
structure ExprComparisonConfig where
  /-- Which kind of equality check to use. -/
  eqKind       : EqKind := .defEq
  /-- What transparency to use for equality checks. -/
  transparency : TransparencyMode := .reducible
deriving Repr, Inhabited

/-- Config data for comparing local contexts. -/
structure LocalDeclComparisonConfig where
  /-- Whether to compare the userNames of two `LocalDecl`s. -/
  checkUserName      : Bool := true
  /-- Whether to compare the types of two `LocalDecl`s. -/
  checkType          : Bool := true
  /-- Whether to compare the letValues of two `ldecl`s. -/
  checkLetValue      : Bool := true
  /-- Whether to compare the binderInfos of two `cdecl`s. -/
  checkBinderInfo    : Bool := true
  /-- Whether to compare the indices of two `LocalDecl`s. -/
  checkIndex         : Bool := false
  /-- Whether to compare the `FVarIds` of two `LocalDecl`s. -/
  checkFVarId        : Bool := false
  /-- Whether to compare the declKinds of a `LocalDecl`. -/
  checkLocalDeclKind : Bool := false
deriving Repr, Inhabited

-- Merge?
/-- Config data for comparing local contexts. -/
structure LocalContextComparisonConfig extends LocalDeclComparisonConfig where
  -- Filtering options
  /-- Whether to include implementation detail decls. -/
  includeImplDetails  : Bool := false
  /-- Whether to include auxiliary decls. -/
  includeAuxDecls     : Bool := false
  /-- Whether to include default decls. -/
  includeDefaultDecls : Bool := true
  /-- Whether to include `ldecls`. -/
  includeLDecls       : Bool := true
  /-- Whether to include `cdecls`. -/
  includeCDecls       : Bool := true
deriving Repr, Inhabited


--!! docs
structure MetavarDeclComparisonConfig where
  checkUserName : Bool := true
  compareLocalContexts? : Option LocalContextComparisonConfig := some {}
  checkTarget : Bool := true
  checkLocalInstances : Bool := true
  checkMetavarKind : Bool := true
  checkIndex : Bool := false
deriving Repr, Inhabited

/-- Config data for comparing two `MVarId`s and, potentially, their decls. -/
structure MVarIdComparisonConfig where
  /-- Whether to compare two `MVarId`s (with `BEq`). -/
  checkMVarId : Bool := false
  /-- Whether to compare the `MetavarDecl`s associated with the `MVarId`s, and if so, how. If
  `none`, the decls are ignored and not accessed. -/
  compareMetavarDecls? : Option MetavarDeclComparisonConfig := some {}
deriving Repr, Inhabited
-- !! Generalize with filtering and mustNotLose,mustNotGain list/array config stuff? Generalize into a goal list config?
inductive FailIfNoProgress.Mode where
/-- Compares the goal lists before and after the tactic. -/
| normal
/-- Only checks if the initial metavariables have been assigned or not. -/
| quick
deriving Repr, Inhabited




-- allow custom functions for comparing `Expr`s etc.? It'd be cool if every comparison function could be overridden, and really was stored in a structure. It'd be neat to do the custom elaborator thing.
/--
--!! Needs updating

Config data for `failIfNoProgress`, `fail_if_no_progress`, and `runAndFailIfNoProgress`.

This determines which aspects of the goals are checked for "progress" and the nature of the
equality checks made.

* `eqKind : EqKind := .defEq` – either `.beq` or `.defEq`; `.beq` uses the instance of `BEq Expr` to
  compare expressions, and `.defEq` uses `isDefEq`
* `transparency : TransparencyMode := .reducible` – the `TransparencyMode` to compare expressions
at.
* `checkTarget : Bool := true` – compare the targets of goals when comparing goals.
* `onLocalInstances : Option LocalInstanceComparisonConfig` – The configuration for comparing local
instances of goals. If `none`, local instances are not compared.
  * `eqKind : EqKind := eqKind`
  * `transparency : TransparencyMode := transparency`
* `onCtx : Option CtxComparisonConfig` – The configuration for comparing local contexts. By default,
  this inherits the given values of `eqKind` and `transparency`, and only checks indices and
  FVarIds if `eqKind := .beq`. If `none`, local contexts are not compared.
  * `eqKind : EqKind := eqKind`
  * `transparency : TransparencyMode := transparency`
  * `checkIndex : Bool := eqKind.isBEq` – checks if the indices (positions) of fvars have changed;
    amounts to checking if some fvars have been made unavialable
  * `checkFVarIds : Bool := eqKind.isBEq` – compares `FVarId`s directly
  * `checkUserNames : Bool := true` – compares the names of fvars in the local context
  * `checkLetValue  : Bool := true` – compares the values of `ldecls`
-/
structure FailIfNoProgress.Config extends ExprComparisonConfig, MetavarDeclComparisonConfig where
  mode : FailIfNoProgress.Mode := .normal
deriving Repr, Inhabited

--!! Does transparency affect BEq or is it only a DefEq thing? I think the latter, but want to be
-- sure.
/-- Compares two expressions according to the given `ComparisonConfig`. -/
def compareExpr (config : ExprComparisonConfig := {}) : Expr → Expr → MetaM Bool :=
  match config with
  | ⟨.beq, _⟩ => fun e₁ e₂ => pure (e₁ == e₂)
  | ⟨.defEq, t⟩ => fun e₁ e₂ => withTransparency t <| withNewMCtxDepth <| isDefEq e₁ e₂

/-- Compares two lists monadically. -/
private def compareListM [Monad m] (c : α → α → m Bool) (l₁ l₂ : List α) : m Bool := do
  unless l₁.length == l₂.length do return false
  l₁.zip l₂ |>.allM fun (a, b) => c a b

/-- Compare two `LocalDecl`s according to `config`. -/
def compareLocalDecl (l₁ l₂ : LocalDecl) (cfg : LocalDeclComparisonConfig := {})
    (ecfg : ExprComparisonConfig) : MetaM Bool :=
  (pure <| (! cfg.checkFVarId   || l₁.fvarId   == l₂.fvarId)
    && (! cfg.checkIndex    || l₁.index    == l₂.index)
    && (! cfg.checkUserName || l₁.userName == l₂.userName)
    && (! cfg.checkLocalDeclKind || l₁.kind == l₂.kind)
    && (! cfg.checkBinderInfo || l₁.binderInfo == l₂.binderInfo))
  <&&> (pure ! (cfg.checkLetValue && l₁.isLet && l₂.isLet) <||> compareExpr ecfg l₁.value l₂.value)
  <&&> (pure ! cfg.checkType <||> compareExpr ecfg l₁.type l₂.type)

/-- Compare two `LocalContext`s according to the specifications in `config`. -/
def compareLCtx (lctx₁ lctx₂ : LocalContext) (cfg : LocalContextComparisonConfig) (ecfg : ExprComparisonConfig) : MetaM Bool := do
  -- Would be slightly better if we could normalize this function given cfg in advance. Likewise elsewhere. And also not filter at all if they're all true.
  let f (d : LocalDecl) :=
    (cfg.includeImplDetails || ! d.isImplementationDetail)
    && (cfg.includeAuxDecls || ! d.isAuxDecl)
    && (cfg.includeCDecls || d.isLet)
    && (cfg.includeLDecls || ! d.isLet)
    && (cfg.includeDefaultDecls || ! (d.kind == .default))
  let l₁ := lctx₁.decls.toList.reduceOption.filter f
  let l₂ := lctx₂.decls.toList.reduceOption.filter f
  compareListM (compareLocalDecl (cfg := cfg.toLocalDeclComparisonConfig) (ecfg := ecfg)) l₁ l₂

instance : BEq MetavarKind where
  beq
  | .natural, .natural | .synthetic, .synthetic | .syntheticOpaque, .syntheticOpaque => true
  | _, _ => false

/-- Compare two `MVarId`s by comparing their types and their local contexts, according to
`config`. -/
def compareMVarId (goal₁ goal₂ : MVarId) (cfg : MetavarDeclComparisonConfig := {})
    (ecfg : ExprComparisonConfig := {}) : MetaM Bool := do
  let decl₁ ← goal₁.getDecl
  let decl₂ ← goal₂.getDecl
  (pure (
    (! cfg.checkIndex || decl₁.index == decl₂.index)
    && (! cfg.checkUserName || decl₁.userName == decl₂.userName)
    && (! cfg.checkMetavarKind || decl₁.kind == decl₂.kind)
    && (! cfg.checkLocalInstances || decl₁.localInstances == decl₂.localInstances)
  ))
  <&&> (pure ! cfg.checkTarget <||> compareExpr ecfg decl₁.type decl₂.type)
  <&&>
    if let some lcfg := cfg.compareLocalContexts? then
      compareLCtx decl₁.lctx decl₂.lctx lcfg ecfg
    else
      pure true

/-- Compare a list of goals to another list of goals. Return false if the number of goals differs,
and otherwise compare the goals pairwise in order according to `config`. -/
def compareGoalList (goals₁ goals₂ : List MVarId) (cfg : MetavarDeclComparisonConfig := {})
    (ecfg : ExprComparisonConfig := {}) : MetaM Bool :=
  compareListM (compareMVarId · · cfg ecfg) goals₁ goals₂

/-- Run `tacs : TacticM Unit` on `goal`, and fail if no progress is made. Return the resulting list of goals otherwise. -/
def runAndFailIfNoProgress (goal : MVarId) (tacs : TacticM Unit)
    (cfg : FailIfNoProgress.Config := {}) : TacticM (List MVarId) := do
  let s ← saveState
  let l ← run goal tacs -- !! correct `run`?
  try -- failing this `try` means we return `l`, and occurs iff progress has been made
    if let .quick := cfg.mode then
      if ← goal.isAssigned then failure -- progress made
    else
      let [newGoal] := l | failure -- progress if number of goals has changed
      -- progress if they are not equivalent goals
      guard <|← compareMVarId goal newGoal cfg.toMetavarDeclComparisonConfig
        cfg.toExprComparisonConfig
  catch _ =>
    return l
  s.restore
  throwError "no progress made on goal:\n{goal}"

/-- Run `tacs`, and fail if no progress is made. Return the result otherwise. -/
def failIfNoProgress (tacs : TacticM α) (cfg : FailIfNoProgress.Config := {}) :
    TacticM α := do
  let s ← saveState
  let goals₁ ← getGoals
  let result ← tacs
  let noProgress ← match cfg.mode with
    | .quick => notM <| goals₁.anyM (·.isAssigned)
    | .normal => do
      let goals₂ ← getGoals
      compareGoalList goals₁ goals₂ cfg.toMetavarDeclComparisonConfig cfg.toExprComparisonConfig
  unless noProgress do return result
  s.restore
  let pluralization := if goals₁.length = 1 then "" else "s"
  throwError "no progress made on goal{pluralization}"

namespace FailIfNoProgress

/-- `fail_if_no_progress tacs` evaluates `tacs`, and fails if no progress is made on the list of
goals. This compares each of their types and local contexts before and after `tacs` is run.

By default, expressions are compared with `isDefEq` at reducible transparency. Any change in the
order or number of goals counts as progress.

`fail_if_no_progress (config := { ... }) tacs` can be used to specify what kind of comparison to
perform. Transparency can be set via the field `transparency`, and the instance for `BEq Expr` can
be used instead of `isDefEq` by specifying `eqKind := .beq`. `BEq` is weaker than `isDefEq`, and
will therefore cause more minor changes to count as "progress". For more configuration options see
`FailIfNoProgress.Config`.
 -/
syntax (name := failIfNoProgress) "fail_if_no_progress " (config)? tacticSeq : tactic

/-- Elaborates `FailIfNoProgress.Config`. -/
declare_config_elab elabConfig Config

elab_rules : tactic
| `(tactic| fail_if_no_progress $[$cfg:config]? $tacs:tacticSeq) => do
  let cfg ← elabConfig (mkOptionalNode cfg)
  Tactic.failIfNoProgress (evalTactic tacs) cfg
