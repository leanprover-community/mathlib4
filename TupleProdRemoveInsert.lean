import Mathlib

open Fin
open Finset
open List

variable [CommMonoid M]

namespace Fin

#check cons
#check snoc

#check prod_cons

@[to_additive (attr := simp), simp]
theorem prod_insertNth (p : Fin n → M) : ∏ j, insertNth i x p j = x * ∏ j, p j := by
  --exact?
  sorry

end Fin

namespace List

#check prod_cons

@[to_additive (attr := simp), simp]
theorem prod_insertIdx {l : List M} (h : i ≤ l.length) : (l.insertIdx i a).prod = a * l.prod := by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    have : l.length > 0 := by exact Nat.zero_lt_of_lt h
    have := exists_cons_of_length_pos this
    obtain ⟨hd, tl, rfl⟩ := this
    · specialize @ih tl (Nat.le_of_lt_succ h)
      simp [ih, mul_left_comm]

end List
namespace List.Vector

section MulOne

variable {M} [Mul M] [One M]

theorem prod_cons {v : List.Vector M n} : (cons a v).toList.prod = a * v.toList.prod := rfl

end MulOne

@[to_additive (attr := simp), simp]
theorem prod_insertIdx {v : List.Vector M n} : (v.insertIdx a i).toList.prod = a * v.toList.prod := by
  apply List.prod_insertIdx
  rw [length_val]
  exact is_le i

end List.Vector
