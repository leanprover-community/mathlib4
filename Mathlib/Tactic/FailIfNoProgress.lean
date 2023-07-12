/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean
import Std
import Mathlib.Lean.Meta.Compare

/-!
# Fail if no progress

This implements the `fail_if_no_progress` tactic (and its internal versions), which fail if no
progress is made by the tactic sequence provided to it.

"Progress" here means a change between the list of goals before the tactics and the list of goals
afterwards, as specified by the settings in `FailIfNoProgress.Config`. By default, only
"observable" changes are checked; this file also provides the preset configs `.anyChanges` and
`.onlyExprs` which check for any changes whatsoever and only compare expressions appearing in the
target and local context, respectively.

This tactic is useful in situations where we want to stop iterating some tactics if they're not
having any  effect, e.g. `repeat (fail_if_no_progress simp <;> ring_nf)`.

## Possible future features

* Tracing to show what progress was made when `fail_if_no_progress` succeeds
  (i.e. `fail_if_no_progress?`)

-/

namespace Mathlib.Tactic.FailIfNoProgress

open Lean Meta Mathlib.Meta Elab Tactic Parser.Tactic

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

/--
Config data for `failIfNoProgress`, `fail_if_no_progress`, and `runAndFailIfNoProgress`. This
determines which aspects of two lists of goals are compared and the nature of the checks made. Any
difference in the compared aspects indicates "progress".

By default, we only compare "observable" properties; internal bookkeeping like `MVarId`s and
`FVarId`s are not checked by default. The following are the fields of this config and its
subconfigs, together with their default values and interpretations.

* `mode := .normal` – If `mode := .normal`, the rest of the config is used to determined equality
as described. If `mode := .quick`, the rest of the config is ignored, and `fail_if_no_progress`
only checks if any of the original goals have been assigned. If not, no progress is considered to
have been made.
* `eqKind := .defEq` – either `.beq` or `.defEq`. `.beq` uses the instance of `BEq Expr` to
  compare expressions, and `.defEq` uses `isDefEq`. Controls all expression comparisons.
* `transparency := .reducible` – the `TransparencyMode` at which to compare expressions; relevant
only if `eqKind := .defEq`. Controls all expression comparisons.
* `checkMVarId := false` – whether to compare the `MVarId`s of two goals.
* `compareMetavarDecls? : Option MetavarDeclComparisonConfig := some {}` – whether to compare the
decl's of two `MVarId`'s, and if so, how. If `none`, the decl's are ignored.

### `MetavarDeclComparisonConfig`

* Properties of the goal's decl to compare:
  * `checkUserName := true`
  * `checkTarget := true`
  * `checkLocalInstances := true`
  * `checkMetavarKind := true`
  * `checkIndex := false`
* `compareLocalContexts? : Option LocalContextComparisonConfig := some {}` – whether to compare the
  local contexts of two metavariables, and if so, how. If `none`, the local contexts are ignored.

### `LocalContextComparisonConfig`

* Filtering options:
  * `includeCDecls := true`
  * `includeLDecls := true`
  * `includeDefaultDecls := true`
  * `includeAuxDecls := false`
  * `includeImplDetails := false` – note that this refers exclusively to `.implDetail`
    `LocalDecl`s, whereas `(·.isImplementationDetail)` refers to both `.implDetail`s and `auxDecl`s.
* Properties of `LocalDecl`s to compare (via extending `LocalDeclComparisonConfig`):
  * `checkUserName := true`
  * `checkType := true`
  * `checkLetValue := true`
  * `checkBinderInfo := true`
  * `checkIndex := false`
  * `checkFVarId := false`
  * `checkLocalDeclKind := false`
-/
structure Config extends ExprComparisonConfig, MVarIdComparisonConfig where
  mode : FailIfNoProgress.Mode := .normal
deriving Repr, Inhabited

/-! ## Preset configs -/

/-- Check for any changes whatsoever. -/
def Config.anyChanges : Config := { MVarIdComparisonConfig.anyChanges with eqKind := .beq }

/-- Only compare expressions in the target and local context. (Does not include implementation
details; does check local instances.) -/
def Config.onlyExprs : Config := { MVarIdComparisonConfig.onlyExprs with }

/-! ## TacticM implementations -/

/-- Run `tacs : TacticM Unit` on `goal`, and fail if no progress is made. Return the resulting list
of goals otherwise. By default, this compares each of their types and local contexts before and
after `tacs` is run; if any changes are seen, "progress" has been made, and the tactics succeed.
Otherwise, we fail.

`cfg` can be used to specify what kind of comparison to perform when checking for "progress". By
default, only "observable" changes are checked. For instance, internal `MVarId`s and `FVarId`s are
not checked, and implementation details are ignored. Expressions are by default compared with
`isDefEq` at reducible transparency. Any change in the order or number of goals counts as progress.

The config preset `FailIfNoProgress.Config.anyChanges` can be used to detect any change;
`FailIfNoProgress.Config.onlyExprs` will only compare expressions in the target and local context.

For more information, see the documentation for `FailIfNoProgress.Config`.
-/
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

/-- Run `tacs`, and fail if no progress is made. Return the result otherwise. By default, this
compares each of their types and local contexts before and after `tacs` is run; if any changes are
seen, "progress" has been made, and the tactics succeed. Otherwise, we fail.

`cfg` can be used to specify what kind of comparison to perform when checking for "progress". By
default, only "observable" changes are checked. For instance, internal `MVarId`s and `FVarId`s are
not checked, and implementation details are ignored. Expressions are by default compared with
`isDefEq` at reducible transparency. Any change in the order or number of goals counts as progress.

The config preset `FailIfNoProgress.Config.anyChanges` can be used to detect any change;
`FailIfNoProgress.Config.onlyExprs` will only compare expressions in the target and local context.

For more information, see the documentation for `FailIfNoProgress.Config`.
-/
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
goals. By default, this compares each of their types and local contexts before and after `tacs` is
run; if any changes are seen, "progress" has been made, and the tactics succeed. Otherwise, we fail.

`fail_if_no_progress (config := { ... }) tacs` can be used to specify what kind of comparison to
perform when checking for "progress". By default, only "observable" changes are checked. For
instance, internal `MVarId`s and `FVarId`s are not checked, and implementation details are ignored.
Expressions are by default compared with `isDefEq` at reducible transparency. Any change in the
order or number of goals counts as progress.

The config preset `FailIfNoProgress.Config.anyChanges` can be used to detect any change;
`FailIfNoProgress.Config.onlyExprs` will only compare expressions in the target and local context.

For more information, see the documentation for `FailIfNoProgress.Config`.
-/
syntax (name := failIfNoProgressSyntax) "fail_if_no_progress " (config)? tacticSeq : tactic

/-- Elaborates `FailIfNoProgress.Config`. -/
declare_config_elab elabConfig Config

elab_rules : tactic
| `(tactic| fail_if_no_progress $[$cfg:config]? $tacs:tacticSeq) => do
  let cfg ← elabConfig (mkOptionalNode cfg)
  failIfNoProgress (evalTactic tacs) cfg
