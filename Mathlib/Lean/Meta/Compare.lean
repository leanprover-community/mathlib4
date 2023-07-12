/-
Copyright (c) 2023 Thomas Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Murrills
-/
import Lean
import Std

/-!
# Configurable comparisons in MetaM

This file defines a number of *configurable comparisons* among elements of common types encountered in metaprogramming.

These structures are often comprised of multiple different fields or components (e.g. a `LocalContext`) or have multiple ways of comparing them (such as using `BEq` or `isDefEq` on `Expr`s), and different circumstances require different notions of equality.

When comparing an element of an atomic type, e.g. `Expr` or `LocalContext`,
`← a₁.compare a₂ cfg` will return `true` if `a₁` is equivalent to `a₂` in the aspects specified by `cfg`. Comparisons among most types also take in an `ecfg : ExprComparisonConfig` specifying how to compare any expressions encountered.

Comparisons may also take in optional state-dependent values to override those inferred in the current state: e.g. `MVarId.compare` can be optionally provided with `MetavarDecl`s for each metavariable, which it will use in lieu of inferring the decl with `(·.getDecl)`.

## Presets

By default, the configs defined here test "user-observable" properties. For instance, actual `MVarId`s and `FVarId`s are ignored by default, as are implementation detail ldecls in the local context. We also provide `.anyChanges` and `.onlyExprs` constructors for all configs, which compare every aspect of the objects and only the expressions appearing in the object, respectively.

## Possible future features

* Different `ExprComparisonConfig`s for each location expressions are compared, ideally with
default propagation from the top level when writing configs, one way or another
* Configs to tweak list comparisons: canLose, canGain, orderless
* Custom overrides for comparison and preprocessing functions via configs
-/

namespace Mathlib.Meta

open Lean Meta Elab

/-! # Configs -/

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
  checkUserName       : Bool := true
  /-- Whether to compare the local contexts of two metavariable decls. -/
  compareLocalContexts? : Option LocalContextComparisonConfig := some {}
  /-- Whether to compare the target (type) of two metavariable decls. -/
  checkTarget         : Bool := true
  /-- Whether to compare the local instances of two metavariable decls. (Uses `BEq` on
  `LocalInstance`.)-/
  checkLocalInstances : Bool := true
  /-- Whether to compare the kinds of two metavariables. -/
  checkMetavarKind    : Bool := true
  /-- Whether to compare the indices of two metavariables. -/
  checkIndex          : Bool := false
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

/-! ### Any changes -/

/-- Check for any changes whatsoever. -/
def LocalDeclComparisonConfig.anyChanges : LocalDeclComparisonConfig where
  checkIndex         := true
  checkFVarId        := true
  checkLocalDeclKind := true

/-- Check for any changes whatsoever. -/
def LocalContextComparisonConfig.anyChanges : LocalContextComparisonConfig where
  includeAuxDecls    := true
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
  checkUserName   := false
  checkBinderInfo := false

/-- Only compare expressions appearing in the local context. (Checks local instances.) -/
def LocalContextComparisonConfig.onlyExprs : LocalContextComparisonConfig where
  toLocalDeclComparisonConfig := .onlyExprs

/-- Only compare expressions appearing in the target and local context. (Does not include
implementation details; does check local instances.) -/
def MetavarDeclComparisonConfig.onlyExprs : MetavarDeclComparisonConfig where
  checkUserName    := false
  checkMetavarKind := false
  compareLocalContexts? := some .onlyExprs

/-- Only compare expressions appearing in the target and local context. (Does not include
implementation details; does check local instances.) -/
def MVarIdComparisonConfig.onlyExprs : MVarIdComparisonConfig where
  compareMetavarDecls? := some .onlyExprs

end Mathlib.Meta

/-! # Comparisons -/

namespace Lean

open Lean Meta Mathlib.Meta

/-- Compares two expressions according to the given `ExprComparisonConfig`. See the documentation
for `ExprComparisonConfig` for more information. -/
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
  -- Would be just slightly better if we could normalize this function given cfg in advance somehow,
  -- and avoid filtering at all if all true. Likewise elsewhere.
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

namespace Mathlib.Meta

open Lean Meta

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

end Mathlib.Meta
