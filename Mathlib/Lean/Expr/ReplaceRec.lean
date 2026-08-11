/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Kim Morrison, Keeley Hoek, Robert Y. Lewis,
Floris van Doorn, Edward Ayers
-/
module -- shake: keep-all

public import Lean.Expr
public import Mathlib.Util.MemoFix

/-!
# ReplaceRec

We define a more flexible version of `Expr.replace` where we can use recursive calls even when
replacing a subexpression. We completely mimic the implementation of `Expr.replace`.
-/

deprecated_module (since := "2026-01-26")

@[expose] public section

namespace Lean.Expr

end Lean.Expr
