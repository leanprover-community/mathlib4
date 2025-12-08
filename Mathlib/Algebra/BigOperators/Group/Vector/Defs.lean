/-
Copyright (c) 2025 Yongshun Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongshun Ye
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Vector.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Sums and products from lists

This file provides basic lemmas for `List.prod` and `List.sum` on `List.Vector`.
-/

namespace List.Vector

variable {M : Type*}

section Mul

variable [Mul M] [One M] {n} {v : List.Vector M n} {a : M}

@[to_additive (attr := simp)]
theorem prod_cons : (cons a v).toList.prod = a * v.toList.prod := rfl -- or `List.prod_cons`

end Mul

end List.Vector
