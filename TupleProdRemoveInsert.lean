import Mathlib

open Fin
open Finset
open List

#check Fin.cons
#check Fin.snoc

#check Fin.prod_cons

example (p : Fin n → ℕ) : ∏ j, insertNth i x p j = x * ∏ j, p j := by
  --exact?
  sorry

#check List.prod_cons

example (l : List ℕ) (h : i < l.length) : (l.insertIdx i a).prod = a * l.prod := by
  --exact?
  sorry

#check List.Vector.prod_cons

example (v : List.Vector ℕ n) : (v.insertIdx a i).toList.prod = a * v.toList.prod := by
  --exact?
  sorry
