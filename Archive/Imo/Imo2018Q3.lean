/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shao Yu
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Real.Archimedean

/-!
# IMO 2018 Q3

Does there exist an anti-Pascal triangle with 2018 rows which contains every integer from \(1\) to \(1+2+\cdots+2018\)?


We have provided the definition of the anti-Pascal triangle.
## TODO
Prove this problem.

-/




/--
Pair each element with the list of its successors.
This is a helper function for the anti-Pascal triangle.
-/
def anti_pascal_triangle_get : List ℤ → List (ℤ × List ℤ)
| [] => []
| x :: xs => (x, xs) :: (anti_pascal_triangle_get xs).map (fun y => y)


/--
Generate the next row of the anti-Pascal triangle by computing absolute differences
between consecutive elements.
-/
def anti_pascal_triangle_first (l : List ℤ) : List ℤ :=
match l with
| [] => []
| x :: xs =>
  (
    List.dropLast (
      (anti_pascal_triangle_get (x :: xs)).map (fun ⟨x, xs⟩ => abs (x - xs.headD 0))
    )
  )


/--
Recursively generate the full anti-Pascal triangle starting from an initial row.
-/
def anti_pascal_triangle_aux (l : List ℤ) : List <| List ℤ :=
match l with
| [] => []
| x :: xs =>
  let l' := anti_pascal_triangle_first (x :: xs)
  l' :: (anti_pascal_triangle_aux l')
termination_by l.length
decreasing_by
  clear l'
  simp only [anti_pascal_triangle_first, List.headD_eq_head?_getD, List.length_dropLast,
    List.length_map, List.length_cons]
  unfold anti_pascal_triangle_get
  simp only [List.map_id_fun', id_eq, List.length_cons, add_tsub_cancel_right]
  induction xs
  · simp [anti_pascal_triangle_get]
  · simp only [List.length_cons]
    simp only [anti_pascal_triangle_get, List.map_id_fun', id_eq, List.length_cons,
      add_lt_add_iff_right]
    assumption


/--
According to the difference property, an anti-Pascal triangle is defined.
-/
def anti_pascal_triangle (l : List ℤ) : List <| List ℤ :=
  l :: List.dropLast (anti_pascal_triangle_aux l)
