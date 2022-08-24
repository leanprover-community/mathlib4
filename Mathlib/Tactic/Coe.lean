/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
-/
import Lean

open Lean Elab Term Meta

/-!
Defines notations for coercions.
1. `↑ t` is defined in core.
2. `(↑)` is equivalent to the eta-reduction of `(↑ ·)`
3. `⇑ t` is a coercion to a function type.
4. `(⇑)` is equivalent to the eta-reduction of `(⇑ ·)`
3. `↥ t` is a coercion to a type.
6. `(↥)` is equivalent to the eta-reduction of `(↥ ·)`
-/

namespace Lean.Elab.Term.CoeImpl

/-- Elaborator for the `(↑)`, `(⇑)`, and `(↥)` notations. -/
def elabPartiallyAppliedCoe (sym : String) (expectedType : Expr) (mkCoe : (b a x : Expr) → TermElabM Expr) : TermElabM Expr := do
  let expectedType ← instantiateMVars expectedType
  let Expr.forallE _ a b .. := expectedType | do
    tryPostpone
    throwError "({sym}) must have a function type, not{indentExpr expectedType}"
  if b.hasLooseBVars then
    tryPostpone
    throwError "({sym}) must have a non-dependent function type, not{indentExpr expectedType}"
  if a.hasExprMVar then tryPostpone
  let f ← withLocalDeclD `x a fun x => do
    mkLambdaFVars #[x] (← mkCoe b a x)
  return f.etaExpanded?.getD f

/-- Partially applied coercion.  Equivalent to the η-reduction of `(↑ ·)` -/
elab "(" "↑" ")" : term <= expectedType =>
  elabPartiallyAppliedCoe "↑" expectedType fun b a x => do
    if b.hasExprMVar then tryPostpone
    mkCoe b a x

/-- `mkFunCoe a x` coerces an expression `x` of type `a` to a function. -/
def mkFunCoe (a x : Expr) : MetaM Expr := do
  let v ← mkFreshLevelMVar
  let type ← mkArrow a (mkSort v)
  let γ ← mkFreshExprMVar type
  let u ← getLevel a
  let coeFunInstType := mkAppN (.const ``CoeFun [u, v]) #[a, γ]
  let inst ← synthInstance coeFunInstType
  expandCoe <| mkAppN (.const ``CoeFun.coe [u, v]) #[a, γ, inst, x]

/-- `⇑ t` coerces `t` to a function. -/
elab "⇑" m:term : term => do
  let x ← elabTerm m none
  mkFunCoe (← inferType x) x

/-- Partially applied function coercion.  Equivalent to the η-reduction of `(⇑ ·)` -/
elab "(" "⇑" ")" : term <= expectedType =>
  elabPartiallyAppliedCoe "⇑" expectedType fun b a x => do
    ensureHasType b (← mkFunCoe a x)

/-- `mkSortCoe a x` coerces an expression `x` of type `a` to a type. -/
def mkSortCoe (a x : Expr) : MetaM Expr := do
  let b ← mkFreshTypeMVar
  let u ← getLevel a
  let v ← getLevel b
  let coeSortInstType := mkAppN (Lean.mkConst ``CoeSort [u, v]) #[a, b]
  let inst ← synthInstance coeSortInstType
  expandCoe <| mkAppN (Lean.mkConst ``CoeSort.coe [u, v]) #[a, b, inst, x]

/-- `↥ t` coerces `t` to a type. -/
elab "↥" t:term : term => do
  let x ← elabTerm t none
  mkSortCoe (← inferType x) x

/-- Partially applied type coercion.  Equivalent to the η-reduction of `(↥ ·)` -/
elab "(" "↥" ")" : term <= expectedType =>
  elabPartiallyAppliedCoe "↥" expectedType fun b a x => do
    ensureHasType b (← mkSortCoe a x)
