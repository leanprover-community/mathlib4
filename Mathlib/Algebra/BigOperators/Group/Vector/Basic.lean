import Mathlib.Data.Vector.Defs
import Mathlib.Data.Vector.Basic

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
