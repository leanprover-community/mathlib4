/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Init
public meta import Lean.Expr
public import Qq
public import Qq.Typ

/-!
# Extra `Qq` helpers

This file contains some additional functions for using the quote4 library more conveniently.
-/

public meta section

open Lean Elab Tactic Meta

namespace Qq

/-- If `e` has type `Sort u` for some level `u`, return `u` and `e : Q(Sort u)`. -/
def getLevelQ (e : Expr) : MetaM (Σ u : Lean.Level, Q(Sort u)) := do
  return ⟨← getLevel e, e⟩

/-- If `e` has type `Type u` for some level `u`, return `u` and `e : Q(Type u)`. -/
def getLevelQ' (e : Expr) : MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let u ← getLevel e
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

/-- Variant of `inferTypeQ` that yields a type in `Type u` rather than `Sort u`.
Throws an error if the type is a `Prop` or if it's otherwise not possible to represent
the universe as `Type u` (for example due to universe level metavariables). -/
-- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Using.20.60QQ.60.20when.20you.20only.20have.20an.20.60Expr.60/near/303349037
def inferTypeQ' (e : Expr) : MetaM ((u : Level) × (α : Q(Type $u)) × Q($α)) := do
  let α ← inferType e
  let ⟨v, α⟩ ← getLevelQ' α
  pure ⟨v, α, e⟩

theorem QuotedDefEq.rfl {u : Level} {α : Q(Sort u)} {a : Q($α)} : @QuotedDefEq u α a a := ⟨⟩

/-- Return a local declaration whose type is definitionally equal to `sort`.

This is a Qq version of `Lean.Meta.findLocalDeclWithType?` -/
def findLocalDeclWithTypeQ? {u : Level} (sort : Q(Sort u)) : MetaM (Option Q($sort)) := do
  let some fvarId ← findLocalDeclWithType? q($sort) | return none
  return some <| .fvar fvarId

/-- Returns a proof of `p : Prop` using `decide p`.

This is a Qq version of `Lean.Meta.mkDecideProof`. -/
def mkDecideProofQ (p : Q(Prop)) : MetaM Q($p) := mkDecideProof p

/-- Join a list of elements of type `α` into a container `β`.

Usually `β` is `q(Multiset α)` or `q(Finset α)` or `q(Set α)`.

As an example
```lean
mkSetLiteralQ q(Finset ℝ) (List.range 4 |>.map fun n : ℕ ↦ q($n•π))
```
produces the expression `{0 • π, 1 • π, 2 • π, 3 • π} : Finset ℝ`.
-/
def mkSetLiteralQ {u v : Level} {α : Q(Type u)} (β : Q(Type v))
    (elems : List Q($α))
    (_ : Q(EmptyCollection $β) := by exact q(inferInstance))
    (_ : Q(Singleton $α $β) := by exact q(inferInstance))
    (_ : Q(Insert $α $β) := by exact q(inferInstance)) :
    Q($β) :=
  match elems with
  | [] => q(∅)
  | [x] => q({$x})
  | x :: xs => q(Insert.insert $x $(mkSetLiteralQ β xs))

/-- Returns the natural number literal `n` as used in the frontend. It is a `OfNat.ofNat`
application. Recall that all theorems and definitions containing numeric literals are encoded using
`OfNat.ofNat` applications in the frontend.

This is a Qq version of `Lean.mkNatLit`. -/
def mkNatLitQ (n : Nat) : Q(Nat) := mkNatLit n

/-- Returns the integer literal `n`.

This is a Qq version of `Lean.mkIntLit`. -/
def mkIntLitQ (n : Int) : Q(Int) := mkIntLit n

end Qq
