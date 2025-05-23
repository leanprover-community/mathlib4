/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
import Mathlib.Init
import Batteries.Data.Rat.Basic
import Batteries.Tactic.Alias

/-!
# Additional operations on Expr and rational numbers

This file defines some operations involving `Expr` and rational numbers.

## Main definitions

* `Lean.Expr.isExplicitNumber`: is an expression a number in normal form?
  This includes natural numbers, integers and rationals.
-/

namespace Lean.Expr

/--
Check if an expression is a "rational in normal form",
i.e. either an integer number in normal form,
or `n / d` where `n` is an integer in normal form, `d` is a natural number in normal form,
`d ≠ 1`, and `n` and `d` are coprime (in particular, we check that `(mkRat n d).den = d`).
If so returns the rational number.
-/
def rat? (e : Expr) : Option Rat := do
  if e.isAppOfArity ``Div.div 4 then
    let d ← e.appArg!.nat?
    guard (d ≠ 1)
    let n ← e.appFn!.appArg!.int?
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    e.int?

/--
Test if an expression represents an explicit number written in normal form:
* A "natural number in normal form" is an expression `OfNat.ofNat n`, even if it is not of type `ℕ`,
  as long as `n` is a literal.
* An "integer in normal form" is an expression which is either a natural number in number form,
  or `-n`, where `n` is a natural number in normal form.
* A "rational in normal form" is an expressions which is either an integer in normal form,
  or `n / d` where `n` is an integer in normal form, `d` is a natural number in normal form,
  `d ≠ 1`, and `n` and `d` are coprime (in particular, we check that `(mkRat n d).den = d`).
-/
def isExplicitNumber : Expr → Bool
  | .lit _ => true
  | .mdata _ e => isExplicitNumber e
  | e => e.rat?.isSome

end Lean.Expr
