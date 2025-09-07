/-
Copyright (c) 2025 Yongshun Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongshun Ye
-/
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic

/-!
# Sums and products from vectors

This file provides basic results analogous to those in `Albegra/BigOperators/Group/List/Basic.lean`
but for `List.Vector`, separated to avoid import cycles.
-/

variable {M : Type*}

namespace List.Vector

section CommMonoid

variable [CommMonoid M] {a : M} {n} {v : List.Vector M n}

@[to_additive (attr := simp)]
theorem prod_insertIdx {i} : (v.insertIdx a i).toList.prod = a * v.toList.prod := by
  apply List.prod_insertIdx
  rw [length_val]
  exact i.is_le

@[to_additive (attr := simp)]
theorem mul_prod_eraseIdx {v : List.Vector M (n + 1)} {i} :
    v.get i * (v.eraseIdx i).toList.prod = v.toList.prod := by
  apply List.mul_prod_eraseIdx

end CommMonoid

end List.Vector
