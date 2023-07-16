/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Alex J. Best
-/
import Qq
import Mathlib.Tactic.ToLevel

/-!
# Extra `Qq` helpers

This file contains some additional functions for using the quote4 library more conveniently.
-/
open Lean Elab Tactic Meta

namespace Qq

/-- Variant of `inferTypeQ` that yields a type in `Type u` rather than `Sort u`.
Throws an error if the type is a `Prop` or if it's otherwise not possible to represent
the universe as `Type u` (for example due to universe level metavariables). -/
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Using.20.60QQ.60.20when.20you.20only.20have.20an.20.60Expr.60/near/303349037
def inferTypeQ' (e : Expr) : MetaM ((u : Level) × (α : Q(Type $u)) × Q($α)) := do
  let α ← inferType e
  let .sort u ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  pure ⟨v, α, e⟩

theorem QE.rfl : @QE u α a a := ⟨⟩

end Qq

open scoped Qq

/-- `Lean.toTypeExpr` with Qq support. -/
def Lean.toTypeExprQ (α : Type u) [Lean.ToLevel.{u}] [Lean.ToExpr α] :
  Q(Type $(Lean.toLevel.{u})) := Lean.toTypeExpr α

/-- `Lean.toExpr` with Qq support. -/
def Lean.toExprQ {α : Type u} [Lean.ToLevel.{u}] [Lean.ToExpr α] (x : α) :
  Q($(toTypeExprQ α)) := Lean.toExpr x

/-- `Lean.toExpr` with Qq support. -/
def Lean.ToExpr.mkQ.{u} {α : Type u} [Lean.ToLevel.{u}]
    (toTypeExprQ : Q(Type $(Lean.toLevel.{u}))) (toExprQ : α → Q($toTypeExprQ)) :
    ToExpr α where
  toTypeExpr := toTypeExprQ
  toExpr x := toExprQ x
