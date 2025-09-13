/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-! ### List.splitOn -/

namespace List

variable {α : Type*} (p : α → Bool) (xs : List α) (ls : List (List α))

attribute [simp] splitAt_eq

@[simp]
theorem splitOn_nil [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl

@[simp]
theorem splitOnP_nil : [].splitOnP p = [[]] :=
  rfl

theorem splitOnP.go_ne_nil (xs acc : List α) : splitOnP.go p xs acc ≠ [] := by
  induction xs generalizing acc <;> simp [go]; split <;> simp [*]

theorem splitOnP.go_acc (xs acc : List α) :
    splitOnP.go p xs acc = modifyHead (acc.reverse ++ ·) (splitOnP p xs) := by
  induction xs generalizing acc with
  | nil => simp only [go, modifyHead, splitOnP_nil, append_nil]
  | cons hd tl ih =>
    simp only [splitOnP, go]; split
    · simp only [modifyHead, reverse_nil, append_nil]
    · rw [ih [hd], modifyHead_modifyHead, ih]
      congr; funext x; simp only [reverse_cons, append_assoc]; rfl

theorem splitOnP_ne_nil (xs : List α) : xs.splitOnP p ≠ [] := splitOnP.go_ne_nil _ _ _

@[simp]
theorem splitOnP_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) := by
  rw [splitOnP, splitOnP.go]; split <;> [rfl; simp [splitOnP.go_acc]]

/-- The original list `L` can be recovered by flattening the lists produced by `splitOnP p L`,
interspersed with the elements `L.filter p`. -/
theorem splitOnP_spec (as : List α) :
    flatten (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    rw [splitOnP_cons, filter]
    by_cases h : p a
    · rw [if_pos h, h, map, cons_append, zipWith, nil_append, flatten, cons_append, cons_inj_right]
      exact ih
    · rw [if_neg h, eq_false_of_ne_true h, flatten_zipWith (splitOnP_ne_nil _ _)
        (append_ne_nil_of_right_ne_nil _ (cons_ne_nil [] [])), cons_inj_right]
      exact ih
where
  flatten_zipWith {xs ys : List (List α)} {a : α} (hxs : xs ≠ []) (hys : ys ≠ []) :
      flatten (zipWith (fun x x_1 ↦ x ++ x_1) (modifyHead (cons a) xs) ys) =
        a :: flatten (zipWith (fun x x_1 ↦ x ++ x_1) xs ys) := by
    cases xs with | nil => contradiction | cons =>
      cases ys with | nil => contradiction | cons => rfl

/-- If no element satisfies `p` in the list `xs`, then `xs.splitOnP p = [xs]` -/
theorem splitOnP_eq_single (h : ∀ x ∈ xs, ¬p x) : xs.splitOnP p = [xs] := by
  induction xs with
  | nil => simp only [splitOnP_nil]
  | cons hd tl ih =>
    simp only [splitOnP_cons, h hd mem_cons_self, if_false, Bool.false_eq_true,
      modifyHead_cons, ih <| forall_mem_of_forall_mem_cons h]

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem splitOnP_first (h : ∀ x ∈ xs, ¬p x) (sep : α) (hsep : p sep) (as : List α) :
    (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p := by
  induction xs with
  | nil => simp [hsep]
  | cons hd tl ih => simp [h hd _, ih <| forall_mem_of_forall_mem_cons h]

/-- `intercalate [x]` is the left inverse of `splitOn x` -/
theorem intercalate_splitOn (x : α) [DecidableEq α] : [x].intercalate (xs.splitOn x) = xs := by
  simp only [intercalate, splitOn]
  induction xs with | nil => simp [flatten] | cons hd tl ih => ?_
  rcases h' : splitOnP (· == x) tl with - | ⟨hd', tl'⟩; · exact (splitOnP_ne_nil _ tl h').elim
  rw [h'] at ih
  rw [splitOnP_cons]
  split_ifs with h
  · rw [beq_iff_eq] at h
    subst h
    simp [ih, flatten, h']
  cases tl' <;> simpa [flatten, h'] using ih

/-- `splitOn x` is the left inverse of `intercalate [x]`, on the domain
consisting of each nonempty list of lists `ls` whose elements do not contain `x` -/
theorem splitOn_intercalate [DecidableEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls := by
  simp only [intercalate]
  induction ls with | nil => contradiction | cons hd tl ih => ?_
  cases tl
  · suffices hd.splitOn x = [hd] by simpa [flatten]
    refine splitOnP_eq_single _ _ ?_
    intro y hy H
    rw [eq_of_beq H] at hy
    refine hx hd ?_ hy
    simp
  · simp only [intersperse_cons₂, singleton_append, flatten]
    specialize ih _ _
    · intro l hl
      apply hx l
      simp only [mem_cons] at hl ⊢
      exact Or.inr hl
    · exact List.noConfusion
    have := splitOnP_first (· == x) hd ?h x (beq_self_eq_true _)
    case h =>
      intro y hy H
      rw [eq_of_beq H] at hy
      exact hx hd (.head _) hy
    simp only [splitOn] at ih ⊢
    rw [this, ih]

end List
