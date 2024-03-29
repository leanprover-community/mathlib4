/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean.HeadIndex
import Lean.Meta.ExprLens
/-! # Find the positions of a pattern in an expression -/

namespace Lean.Meta

/-- Return the positions that `kabstract` would abstract.
i.e. the positions that unify with the pattern -/
def kabstractPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let e ← instantiateMVars e
  let mctx ← getMCtx
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos → MetaM (Array SubExpr.Pos) :=
      match e with
      | .app f a         => visit f pos.pushAppFn
                        >=> visit a pos.pushAppArg
      | .mdata _ b       => visit b pos
      | .proj _ _ b      => visit b pos.pushProj
      | .letE _ t v b _  => visit t pos.pushLetVarType
                        >=> visit v pos.pushLetValue
                        >=> visit b pos.pushLetBody
      | .lam _ d b _     => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | _                => pure
    if e.hasLooseBVars || e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      if (← isDefEq e p) then
        setMCtx mctx
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]

/-- Return the subexpression at position `pos` in `e` together with an occurrence number
that allows the expression to be found by `kabstract`.
Return `none` when the subexpression contains loose bound variables. -/
def viewKAbstractSubExpr (e : Expr) (pos : SubExpr.Pos) : MetaM (Option (Expr × Option Nat)) := do
  let subExpr ← Core.viewSubexpr pos e
  if e.hasLooseBVars then
    return none
  let positions ← kabstractPositions subExpr e
  let some n := positions.getIdx? pos | unreachable!
  return some (subExpr, if positions.size == 1 then none else some (n + 1))
