import Mathlib

open Fin
open Finset
open List

variable [CommMonoid M]

namespace Fin

#check Fin.cons
#check Fin.snoc

#check Fin.prod_cons

@[to_additive (attr := simp), simp]
theorem prod_insertNth (p : Fin n → M) : ∏ j, insertNth i x p j = x * ∏ j, p j := by
  --exact?
  sorry

end Fin

namespace List

#check List.prod_cons

@[to_additive (attr := simp), simp]
theorem prod_insertIdx (l : List M) (h : i < l.length) : (l.insertIdx i a).prod = a * l.prod := by
  --exact?
  sorry

end List
namespace List.Vector

section MulOne

variable {M} [Mul M] [One M]

theorem prod_cons (v : List.Vector M n) : (cons a v).toList.prod = a * v.toList.prod := rfl

end MulOne

@[to_additive (attr := simp), simp]
theorem prod_insertIdx (v : List.Vector M n) : (v.insertIdx a i).toList.prod = a * v.toList.prod := by
  --exact?
  sorry

end List.Vector
