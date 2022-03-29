/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Scott Morrison, Keeley Hoek, Robert Y. Lewis, Floris van Doorn, E.W.Ayers
-/
import Lean
import Lean.Meta
import Mathlib.Util.TermUnsafe
import Mathlib.Lean.Expr.Traverse
import Mathlib.Util.MemoFix
namespace Lean.Expr
/-!
# ReplaceRec

We define a more flexible version of `Expr.replace` where we can use recursive calls even when
replacing a subexpression. We completely mimic the implementation of `Expr.replace`. -/

/-- A version of `Expr.replace` where the replacement function is available to the function `f?`.

`replaceRec f? e` will call `f? r e` where `r = replaceRec f?`.
If `f? r e = none` then `r` will be called on each immediate subexpression of `e` and reassembled.
If it is `some x`, traversal terminates and `x` is returned.
If you wish to recursively replace things in the implementation of `f?`, you can apply `r`.

The function is also memoised, which means that if the
same expression (by reference) is encountered the cached replacement is used. -/
def replaceRec (f? : (Expr → Expr) → Expr → Option Expr) : Expr → Expr :=
  memoFix fun r e =>
    match f? r e with
    | some x => x
    | none   => traverseChildren (M := Id) r e

/-- A version of `Expr.replace` where we can use recursive calls even if we replace a subexpression.
  When reaching a subexpression `e` we call `traversal e` to see if we want to do anything with this
  expression. If `traversal e = none` we proceed to the children of `e`. If
  `traversal e = some (#[e₁, ..., eₙ], g)`, we first recursively apply this function to
  `#[e₁, ..., eₙ]` to get new expressions `#[f₁, ..., fₙ]`.
  Then we replace `e` by `g [f₁, ..., fₙ]`.

  Important: In order for this function to terminate, the `[e₁, ..., eₙ]` must all be smaller than
  `e` according to some measure  (and this measure must also be strictly decreasing on the w.r.t.
  the structural subterm relation).
  -/
def replaceRecTraversal (traversal : Expr → Option (Array Expr × (Array Expr → Expr))) : Expr → Expr :=
  replaceRec fun r e =>
    match traversal e with
    | none => none
    | some (get, set) => some <| set <| .map r <| get

end Lean.Expr
