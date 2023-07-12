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





namespace Mathlib.Meta

open Lean Meta Elab

/-- Specifies which type of equality check to use on `Expr`s: either `.beq` or `.defEq`. -/
inductive EqKind where
/-- Compare `Expr`s with the instance of `BEq Expr`. -/
| beq
/-- Compare `Expr`s with `isDefEq`. -/
| defEq
deriving Repr, Inhabited

/-- Returns `true` if using `BEq` (`.beq`) and `false` if using `isDefEq` (`.defEq`). -/
def EqKind.isBEq : EqKind → Bool
| .beq   => true
| .defEq => false

/-- Config data for comparing expressions. -/
structure ExprComparisonConfig where
  /-- Which kind of equality check to use on `Expr`s: either `.beq` for `BEq` or `.defEq` for
  `isDefEq`. -/
  eqKind       : EqKind := .defEq
  /-- The transparency to use for equality checks. -/
  transparency : TransparencyMode := .reducible
deriving Repr, Inhabited

/-- Config data for comparing `LocalDecl`s. -/
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

/-- Config data for comparing local contexts. `include*` fields allow filtering of the local
context's list of decls. -/
structure LocalContextComparisonConfig extends LocalDeclComparisonConfig where
  /-- Whether to include `implDetail` decls. (Note that `(·.isImplementationDetail)` refers to both
  `.implDetail`s and `.auxDecl`s; see `includeAuxDecls`.) -/
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


/-- Config data for comparing the `MetavarDecl`s of two metavariables. -/
structure MetavarDeclComparisonConfig where
  /-- Whether to compare the `userName` of two metavariables. -/
  checkUserName : Bool := true
  /-- Whether to compare the local contexts of two metavariable decls. -/
  compareLocalContexts? : Option LocalContextComparisonConfig := some {}
  /-- Whether to compare the target (type) of two metavariable decls. -/
  checkTarget : Bool := true
  /-- Whether to compare the local instances of two metavariable decls. (Uses `BEq` on
  `LocalInstance`.)-/
  checkLocalInstances : Bool := true
  /-- Whether to compare the kinds of two metavariables. -/
  checkMetavarKind : Bool := true
  /-- Whether to compare the indices of two metavariables. -/
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

/-! ## Preset Configs -/

/-! ### Any Changes -/

/-- Check for any changes whatsoever. -/
def LocalDeclComparisonConfig.anyChanges : LocalDeclComparisonConfig where
  checkIndex := true
  checkFVarId := true
  checkLocalDeclKind := true

/-- Check for any changes whatsoever. -/
def LocalContextComparisonConfig.anyChanges : LocalContextComparisonConfig where
  includeAuxDecls := true
  includeImplDetails := true
  toLocalDeclComparisonConfig := .anyChanges

/-- Check for any changes whatsoever. -/
def MetavarDeclComparisonConfig.anyChanges : MetavarDeclComparisonConfig where
  checkIndex := true
  compareLocalContexts? := some .anyChanges

/-- Check for any changes whatsoever. -/
def MVarIdComparisonConfig.anyChanges : MVarIdComparisonConfig where
  checkMVarId := true
  compareMetavarDecls? := some .anyChanges

/-! ### Only expressions -/

/-- Only compare expressions appearing in a local decl. -/
def LocalDeclComparisonConfig.onlyExprs : LocalDeclComparisonConfig where
  checkUserName := false
  checkBinderInfo := false

/-- Only compare expressions appearing in the local context. (Checks local instances.) -/
def LocalContextComparisonConfig.onlyExprs : LocalContextComparisonConfig where
  toLocalDeclComparisonConfig := .onlyExprs

/-- Only compare expressions appearing in the target and local context. (Does not include implementation details; does check local instances.) -/
def MetavarDeclComparisonConfig.onlyExprs : MetavarDeclComparisonConfig where
  checkUserName := false
  checkMetavarKind := false
  compareLocalContexts? := some .onlyExprs

/-- Only compare expressions appearing in the target and local context. (Does not include implementation details; does check local instances.) -/
def MVarIdComparisonConfig.onlyExprs : MVarIdComparisonConfig where
  compareMetavarDecls? := some .onlyExprs



end Mathlib.Meta

namespace Lean

open Lean Meta Mathlib.Meta

/-- Compares two expressions according to the given `ExprComparisonConfig`. See the documentation for `ExprComparisonConfig` for more information. -/
def Expr.compare (e₁ e₂ : Expr) (config : ExprComparisonConfig := {}) : MetaM Bool :=
  match config with
  | ⟨.beq, _⟩ => pure (e₁ == e₂)
  | ⟨.defEq, t⟩ => withTransparency t <| withNewMCtxDepth <| isDefEq e₁ e₂

/-- Compares two lists monadically. Does not check length first. Unrelated to `ListM`. -/
private def compareListM (eq : α → α → MetaM Bool) (l₁ l₂ : List α) : MetaM Bool :=
  l₁.zip l₂ |>.allM fun (a, b) => eq a b

/-- Compare two `LocalDecl`s according to the configs. The settings in `ExprComparisonConfig` will
be used when comparing expressions. -/
def LocalDecl.compare (l₁ l₂ : LocalDecl) (cfg : LocalDeclComparisonConfig := {})
    (ecfg : ExprComparisonConfig) : MetaM Bool :=
  -- withTraceNode `Meta.compare (fun _ => pure "comparing LocalDecls:") <|
  (pure <| (! cfg.checkFVarId   || l₁.fvarId   == l₂.fvarId)
    && (! cfg.checkIndex    || l₁.index    == l₂.index)
    && (! cfg.checkUserName || l₁.userName == l₂.userName)
    && (! cfg.checkLocalDeclKind || l₁.kind == l₂.kind)
    && (! cfg.checkBinderInfo || l₁.binderInfo == l₂.binderInfo))
  <&&> (pure ! (cfg.checkLetValue && l₁.isLet && l₂.isLet) <||> l₁.value.compare l₂.value)
  <&&> (pure ! cfg.checkType <||> l₁.type.compare l₂.type ecfg)

/-- Compare two `LocalDecl`s according to the configs. The settings in `ExprComparisonConfig` will
be used when comparing expressions. -/
def LocalContext.compare (lctx₁ lctx₂ : LocalContext)
    (cfg : LocalContextComparisonConfig) (ecfg : ExprComparisonConfig) : MetaM Bool := do
  -- !! Would be slightly better if we could normalize this function given cfg in advance somehow.
  -- Likewise elsewhere. And also not filter at all if they're all true.
  let f (d : LocalDecl) :=
    (cfg.includeImplDetails || ! d.kind == .implDetail)
    && (cfg.includeAuxDecls || ! d.isAuxDecl)
    && (cfg.includeCDecls || d.isLet)
    && (cfg.includeLDecls || ! d.isLet)
    && (cfg.includeDefaultDecls || ! (d.kind == .default))
  let l₁ := lctx₁.decls.toList.reduceOption.filter f
  let l₂ := lctx₂.decls.toList.reduceOption.filter f
  if l₁.length ≠ l₂.length then return false
  compareListM (·.compare · cfg.toLocalDeclComparisonConfig ecfg) l₁ l₂

-- !! move?
instance : BEq MetavarKind where beq
  | .natural, .natural | .synthetic, .synthetic | .syntheticOpaque, .syntheticOpaque => true
  | _, _ => false

/-- Compare two `MVarId`s by comparing their types and their local contexts, according to
`config`. -/
def MetavarDecl.compare (decl₁ decl₂ : MetavarDecl)
    (cfg : MetavarDeclComparisonConfig := {}) (ecfg : ExprComparisonConfig := {}) : MetaM Bool := do
  (pure <| (! cfg.checkIndex || decl₁.index == decl₂.index)
    && (! cfg.checkUserName || decl₁.userName == decl₂.userName)
    && (! cfg.checkMetavarKind || decl₁.kind == decl₂.kind)
    && (! cfg.checkLocalInstances || decl₁.localInstances == decl₂.localInstances))
  <&&> (pure ! cfg.checkTarget <||> decl₁.type.compare decl₂.type ecfg)
  <&&> do
    let some lcfg := cfg.compareLocalContexts? | pure true
    decl₁.lctx.compare decl₂.lctx lcfg ecfg

/-- Compare a metavariable to another metavariable according to the configs. The settings in
`ExprComparisonConfig` will be used when comparing expressions.

A decl can be provided for each goal as an override for `goal.getDecl`. This is useful when the
goals ought to be compared across two different monad states: then the decl's can be obtained at
the right time and passed in later.
-/
def MVarId.compare (goal₁ goal₂ : MVarId) (cfg : MVarIdComparisonConfig := {})
    (ecfg : ExprComparisonConfig := {}) (decl₁ decl₂ : Option MetavarDecl := none)
    : MetaM Bool := do
  pure (! cfg.checkMVarId || goal₁ == goal₂)
  <&&> do
    let some mdcfg := cfg.compareMetavarDecls? | pure true
    let decl₁ ← decl₁.getDM goal₁.getDecl
    let decl₂ ← decl₂.getDM goal₂.getDecl
    decl₁.compare decl₂ mdcfg ecfg

end Lean

namespace Mathlib

open Lean Meta Elab Tactic Parser.Tactic

namespace Meta

/-- Compare a list of goals to another list of goals. Return false if the number of goals differs,
and otherwise compare the goals pairwise in order according to the configs.

A list of decls can be provided for each list of goals as an override for `goals.mapM (·.getDecl)`.
This is useful when the goals ought to be compared across two different monad states: then the
decl's can be obtained at the right time and passed in later. This does not check that
`goalsᵢ.length == declsᵢ.length`.
-/
def compareGoalList (goals₁ goals₂ : List MVarId) (cfg : MVarIdComparisonConfig := {})
    (ecfg : ExprComparisonConfig := {}) (decls₁ decls₂ : Option (List MetavarDecl) := none)
    : MetaM Bool :=
  (pure <| (goals₁.length == goals₂.length)
    && (! cfg.checkMVarId || goals₁ == goals₂))
  <&&> do
    let some mdcfg := cfg.compareMetavarDecls? | pure true
    let decls₁ ← decls₁.getDM <| goals₁.mapM (·.getDecl)
    let decls₂ ← decls₂.getDM <| goals₂.mapM (·.getDecl)
    compareListM (·.compare · mdcfg ecfg) decls₁ decls₂

end Meta

namespace Tactic.FailIfNoProgress

/-- The overall mode for a `FailIfNoProgress` config. If `mode := .normal`, the rest of the config
is used to determined equality as described. If `mode := .quick`, the rest of the config is
ignored, and `fail_if_no_progress` only checks if any of the original goals have been assigned. If
not, no progress is considered to have been made. -/
inductive Mode where
/-- Compares the goal lists before and after the tactic using the given config settings. -/
| normal
/-- Only checks if the initial metavariables have been assigned or not. If this mode is used, no
other checks are performed. -/
| quick
deriving Repr, Inhabited

structure Config extends ExprComparisonConfig, MVarIdComparisonConfig where
  mode : FailIfNoProgress.Mode := .normal
deriving Repr, Inhabited

/-! ## Preset configs -/

/-- Check for any changes whatsoever. -/
def Config.anyChanges : Config := { MVarIdComparisonConfig.anyChanges with eqKind := .beq }

/-- Only compare expressions in the target and local context. (Does not include implementation details; does check local instances.) -/
def Config.onlyExprs : Config := { MVarIdComparisonConfig.onlyExprs with }

/-! ## TacticM implementations -/
def runAndFailIfNoProgress (goal : MVarId) (tacs : TacticM Unit)
    (cfg : FailIfNoProgress.Config := {}) : TacticM (List MVarId) := do
  let decl ← goal.getDecl
  let l ← run goal tacs
  try -- failing this `try` means we return `l`, and occurs iff progress has been made
    if let .quick := cfg.mode then
      if ← goal.isAssigned then failure -- progress
    else
      let [newGoal] := l | failure -- progress
      guard <|← goal.compare newGoal cfg.toMVarIdComparisonConfig
        cfg.toExprComparisonConfig decl
  catch _ =>
    return l
  let resultMsg ← match cfg.mode with
  | .quick => pure m!"no goals were assigned"
  | .normal => do pure m!"obtained\n{← getGoals}"
  throwError "no progress made on goal; {resultMsg}"

/-- Run `tacs`, and fail if no progress is made. Return the result otherwise. -/
def failIfNoProgress (tacs : TacticM α) (cfg : FailIfNoProgress.Config := {}) :
    TacticM α := do
  let goals₁ ← getGoals
  let decls₁ ← goals₁.mapM (·.getDecl)
  let result ← tacs
  let progress ← match cfg.mode with
    | .quick => goals₁.anyM (·.isAssigned)
    | .normal => do
      let goals₂ ← getGoals
      notM <|
        compareGoalList goals₁ goals₂ cfg.toMVarIdComparisonConfig cfg.toExprComparisonConfig decls₁
  if progress then
    return result
  else
    let resultMsg ← match cfg.mode with
      | .quick => pure m!"no goals were assigned"
      | .normal => do pure m!"obtained\n{← getGoals}"
    let pluralization := if goals₁.length = 1 then "" else "s"
    throwError "no progress made on goal{pluralization}; {resultMsg}"


/-! ## Tactic syntax implementation -/

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
syntax (name := failIfNoProgressSyntax) "fail_if_no_progress " (config)? tacticSeq : tactic

/-- Elaborates `FailIfNoProgress.Config`. -/
declare_config_elab elabConfig Config

elab_rules : tactic
| `(tactic| fail_if_no_progress $[$cfg:config]? $tacs:tacticSeq) => do
  let cfg ← elabConfig (mkOptionalNode cfg)
  failIfNoProgress (evalTactic tacs) cfg
