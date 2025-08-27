import Mathlib

open Nat

namespace List

theorem getElem_scanl_eq_foldl_take {α} {f} {a : α} (l : List α) (i : ℕ) (h : i < (l.scanl f a).length) :
    (l.scanl f a)[i] = (l.take i).foldl f a := by
  induction i
  case zero => simp
  case succ i ih =>
    specialize ih (lt_of_succ_lt h)

    sorry

lemma lt_scanl_length_of_lt_length_add_one {l : List α} (h : i < l.length + 1) : i < (l.scanl f a).length :=
  lt_of_lt_of_eq h (l.length_scanl a).symm

lemma lt_scanl_length_of_le_length {l : List α} (h : i ≤ l.length) : i < (l.scanl f a).length :=
  lt_scanl_length_of_lt_length_add_one (lt_add_one_of_le h)

/-- an alternative taking `i < l.length + 1` -/
theorem getElem_scanl_eq_foldl_take' {α} {f} {a : α} (l : List α) (i : ℕ) (h : i < l.length + 1) :
    getElem (l.scanl f a) i (lt_scanl_length_of_lt_length_add_one h) = (l.take i).foldl f a :=
  getElem_scanl_eq_foldl_take l i (lt_scanl_length_of_lt_length_add_one h)

/-- another alternative with `i ≤ l.length` -/
theorem getElem_scanl_eq_foldl_take'' {α} {f} {a : α} (l : List α) (i : ℕ) (h : i ≤ l.length) :
    getElem (l.scanl f a) i (lt_scanl_length_of_le_length h) = (l.take i).foldl f a :=
  getElem_scanl_eq_foldl_take l i (lt_scanl_length_of_le_length h)

theorem get_scanl_eq_foldl_take {α} {f} {a : α} (l : List α) (i : Fin (l.length + 1)) :
    (l.scanl f a).get (i.cast (l.length_scanl a).symm) = (l.take i).foldl f a := by
  apply getElem_scanl_eq_foldl_take'
  exact i.isLt

end List
