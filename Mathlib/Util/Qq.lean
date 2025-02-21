/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Alex J. Best, Yaël Dillies
-/
import Mathlib.Lean.Expr.Lit
import Qq

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

theorem QuotedDefEq.rfl {u : Level} {α : Q(Sort u)} {a : Q($α)} : @QuotedDefEq u α a a := ⟨⟩

/-- Return a local declaration whose type is definitionally equal to `sort`.

This is a Qq version of `Lean.Meta.findLocalDeclWithType?` -/
def findLocalDeclWithTypeQ? {u : Level} (sort : Q(Sort u)) : MetaM (Option Q($sort)) := do
  let some fvarId ← findLocalDeclWithType? q($sort) | return none
  return some <| .fvar fvarId

/-- Returns the natural number from a natural literal expression, or `none` if the expression isn't
a natural literal.

See `Lean.Expr.rawNatLit?` for a `MetaM`-less version of this function that only checks for raw
literals. -/
def natLitQq? : Q(Nat) → MetaM (Option Nat)
  | ~q(OfNat.ofNat $n) => pure n.rawNatLit?
  | e => pure e.rawNatLit?

/-- Returns the integer from a integer literal expression, or `none` if the expression isn't
an integer literal.

See `Lean.Expr.rawIntLit?` for a `MetaM`-less version of this function that only checks for raw
literals. -/
def intLitQq? : Q(Int) → MetaM (Option Int)
  | ~q(OfNat.ofNat $n) => pure n.rawNatLit?
  | e => pure e.rawIntLit?

end Qq
