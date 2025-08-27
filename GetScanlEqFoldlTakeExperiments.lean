import Mathlib

theorem get_scanl_eq_foldl_take {α} {f} {a : α} (l : List α) (i : Fin (l.length + 1)) :
    (l.scanl f a).get (i.cast (l.length_scanl a).symm) = (l.take i).foldl f a := by
  sorry
