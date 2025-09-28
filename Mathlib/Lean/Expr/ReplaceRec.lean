/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Kim Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, Edward Ayers
-/
import Lean.Expr
import Mathlib.Util.MemoFix

/-!
# ReplaceRec

We define a more flexible version of `Expr.replace` where we can use recursive calls even when
replacing a subexpression. We completely mimic the implementation of `Expr.replace`.
-/

namespace Lean.Expr

/-- A version of `Expr.replace` where the replacement function is available to the function `f?`.

`replaceRec f? e` will call `f? r e` where `r = replaceRec f?`.
If `f? r e = none` then `r` will be called on each immediate subexpression of `e` and reassembled.
If it is `some x`, traversal terminates and `x` is returned.
If you wish to recursively replace things in the implementation of `f?`, you can apply `r`.

The function is also memoised, which means that if the
same expression (by reference) is encountered the cached replacement is used. -/
def replaceRec (f? : (Expr → Expr) → Expr → Option Expr) : Expr → Expr :=
  memoFix fun r e ↦
    match f? r e with
    | some x => x
    | none   => Id.run <| traverseChildren (pure <| r ·) e

end Lean.Expr
