import Mathlib

open Fin
open Finset
open List

#check Fin.cons
#check Fin.snoc

example (p : Fin n → ℕ) : ∏ j, insertNth i x p j = x * ∏ j, p j := by
  --exact?
  sorry

example (l : List ℕ) (h : i < l.length) : (l.insertIdx i a).prod = a * l.prod := by
  --exact?
  sorry
