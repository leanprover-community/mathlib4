/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Qq

/-!
# Extract literals from expressions

This file provides extra utility function to extract raw natural and integer literals from
expressions.
-/

open Lean

namespace Lean.Expr

/-- Returns the integer from a raw integer literal expression, or `none` if the expression isn't
a raw integer literal.

See `Qq.intLitQq?` for a Qq version of this that also handles non-raw literals. -/
def rawIntLit? (e : Expr) : Option Int :=
  if e.isAppOfArity ``Int.ofNat 1 then
    e.appArg!.rawNatLit?
  else if e.isAppOfArity ``Int.negOfNat 1 then
    e.appArg!.rawNatLit?.map .negOfNat
  else
    none

/-- Returns the natural number from a raw natural literal expression. Panics if the expression isn't
a raw natural literal.

See `Qq.natLitQq?` for a Qq version of this that also handles non-raw literals.

Note this is equivalent to `Lean.Expr.natLit!`, which is misnamed. -/
def rawNatLit! (e : Expr) : Nat :=
  match e.rawNatLit? with
  | some n => n
  | none => panic! "not a raw natural literal"

@[simp] theorem rawNatLit!_lit_natVal (n : Nat) : rawNatLit! (.lit <| .natVal n) = n := rfl

/-- Returns the integer number from a raw natural literal expression. Panics if the expression isn't
a raw integer literal.

See `Qq.intLitQq?` for a Qq version of this that also handles non-raw literals.

Note this is equivalent to `Lean.Expr.intLit!`, which is misnamed. -/
def rawIntLit! (e : Expr) : Int :=
  match e.rawIntLit? with
  | some n => n
  | none => panic! "not a raw integer literal"

end Lean.Expr
