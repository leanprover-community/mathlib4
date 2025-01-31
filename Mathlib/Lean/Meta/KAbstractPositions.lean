/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init
import Lean.HeadIndex
import Lean.Meta.ExprLens
import Lean.Meta.Check

/-!

# Find the positions of a pattern in an expression

This file defines some tools for dealing with sub expressions and occurrence numbers.
This is used for creating a `rw` tactic call that rewrites a selected expression.

`viewKAbstractSubExpr` takes an expression and a position in the expression, and returns
the sub-expression together with an optional occurrence number that would be required to find
the sub-expression using `kabstract` (which is what `rw` uses to find the position of the rewrite)

`rw` can fail if the motive is not type correct. `kabstractIsTypeCorrect` checks
whether this is the case.

-/

namespace Lean.Meta

/-- Return the positions that `kabstract` would abstract for pattern `p` in expression `e`.
i.e. the positions that unify with `p`. -/
def kabstractPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let e ← instantiateMVars e
  let mctx ← getMCtx
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec
  /-- The main loop that loops through all subexpressions -/
  visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos → MetaM (Array SubExpr.Pos) :=
      match e with
      | .app fn arg                  => visit fn pos.pushAppFn
                                    >=> visit arg pos.pushAppArg
      | .mdata _ expr                => visit expr pos
      | .proj _ _ struct             => visit struct pos.pushProj
      | .letE _ type value body _    => visit type pos.pushLetVarType
                                    >=> visit value pos.pushLetValue
                                    >=> visit body pos.pushLetBody
      | .lam _ binderType body _     => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | .forallE _ binderType body _ => visit binderType pos.pushBindingDomain
                                    >=> visit body pos.pushBindingBody
      | _                            => pure
    if e.hasLooseBVars then
      visitChildren positions
    else if e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      if ← isDefEq e p then
        setMCtx mctx -- reset the `MetavarContext` because `isDefEq` can modify it if it succeeds
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]

/-- Return the subexpression at position `pos` in `e` together with an occurrence number
that allows the expression to be found by `kabstract`.
Return `none` when the subexpression contains loose bound variables. -/
def viewKAbstractSubExpr (e : Expr) (pos : SubExpr.Pos) : MetaM (Option (Expr × Option Nat)) := do
  let subExpr ← Core.viewSubexpr pos e
  if subExpr.hasLooseBVars then
    return none
  let positions ← kabstractPositions subExpr e
  let some n := positions.idxOf? pos | unreachable!
  return some (subExpr, if positions.size == 1 then none else some (n + 1))

/-- Determine whether the result of abstracting `subExpr` from `e` at position `pos` results
in a well typed expression. This is important if you want to rewrite at this position.

Here is an example of what goes wrong with an ill-typed kabstract result:

```
example (h : [5] ≠ []) : List.getLast [5] h = 5 := by
  rw [show [5] = [5] from rfl] -- tactic 'rewrite' failed, motive is not type correct
```
-/
def kabstractIsTypeCorrect (e subExpr : Expr) (pos : SubExpr.Pos) : MetaM Bool := do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
    isTypeCorrect (← replaceSubexpr (fun _ => pure fvar) pos e)

end Lean.Meta
