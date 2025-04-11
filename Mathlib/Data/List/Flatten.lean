/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak
-/
import Mathlib.Data.List.Induction

/-!
# Join of a list of lists

This file proves basic properties of `List.flatten`, which concatenates a list of lists. It is
defined in `Init.Data.List.Basic`.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α β : Type*}

namespace List

@[gcongr]
protected theorem Sublist.flatten {l₁ l₂ : List (List α)} (h : l₁ <+ l₂) :
    l₁.flatten <+ l₂.flatten := by
  induction h with
  | slnil => simp
  | cons _ _ ih =>
    rw [flatten_cons]
    exact ih.trans (sublist_append_right _ _)
  | cons₂ _ _ ih => simpa

@[gcongr]
protected theorem Sublist.flatMap {l₁ l₂ : List α} (h : l₁ <+ l₂) (f : α → List β) :
    l₁.flatMap f <+ l₂.flatMap f :=
  (h.map f).flatten

set_option linter.deprecated false in
/-- See `List.length_flatten` for the corresponding statement using `List.sum`. -/
@[deprecated length_flatten (since := "2024-10-17")]
lemma length_flatten' (L : List (List α)) : length (flatten L) = Nat.sum (map length L) := by
  induction L <;> [rfl; simp only [*, flatten, map, Nat.sum_cons, length_append]]

@[deprecated (since := "2024-10-25")] alias length_join' := length_flatten'

set_option linter.deprecated false in
/-- See `List.countP_flatten` for the corresponding statement using `List.sum`. -/
@[deprecated countP_flatten (since := "2024-10-17")]
lemma countP_flatten' (p : α → Bool) :
    ∀ L : List (List α), countP p L.flatten = Nat.sum (L.map (countP p))
  | [] => rfl
  | a :: l => by rw [flatten, countP_append, map_cons, Nat.sum_cons, countP_flatten' _ l]

@[deprecated (since := "2024-10-25")] alias countP_join' := countP_flatten'

set_option linter.deprecated false in
/-- See `List.count_flatten` for the corresponding statement using `List.sum`. -/
@[deprecated count_flatten (since := "2024-10-17")]
lemma count_flatten' [BEq α] (L : List (List α)) (a : α) :
    L.flatten.count a = Nat.sum (L.map (count a)) := countP_flatten' _ _

@[deprecated (since := "2024-10-25")] alias count_join' := count_flatten'

set_option linter.deprecated false in
/-- See `List.length_flatMap` for the corresponding statement using `List.sum`. -/
@[deprecated "Use `List.length_flatMap`." (since := "2024-10-17")]
lemma length_flatMap' (l : List α) (f : α → List β) :
    length (l.flatMap f) = Nat.sum (map (length ∘ f) l) := by
  rw [List.flatMap, length_flatten', map_map]

@[deprecated (since := "2024-10-16")] alias length_bind' := length_flatMap'

set_option linter.deprecated false in
/-- See `List.countP_flatMap` for the corresponding statement using `List.sum`. -/
@[deprecated "Use `List.countP_flatMap`." (since := "2024-10-17")]
lemma countP_flatMap' (p : β → Bool) (l : List α) (f : α → List β) :
    countP p (l.flatMap f) = Nat.sum (map (countP p ∘ f) l) := by
  rw [List.flatMap, countP_flatten', map_map]

@[deprecated (since := "2024-10-16")] alias countP_bind' := countP_flatMap'

set_option linter.deprecated false in
/-- See `List.count_flatMap` for the corresponding statement using `List.sum`. -/
@[deprecated "Use `List.count_flatMap`." (since := "2024-10-17")]
lemma count_flatMap' [BEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.flatMap f) = Nat.sum (map (count x ∘ f) l) := countP_flatMap' _ _ _

@[deprecated (since := "2024-10-16")] alias count_bind' := count_flatMap'

set_option linter.deprecated false in
/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists.

See `List.take_sum_flatten` for the corresponding statement using `List.sum`. -/
@[deprecated "Use `List.take_sum_flatten`." (since := "2024-10-17")]
theorem take_sum_flatten' (L : List (List α)) (i : ℕ) :
    L.flatten.take (Nat.sum ((L.map length).take i)) = (L.take i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_append, *]

@[deprecated (since := "2024-10-25")] alias take_sum_join' := take_sum_flatten'

set_option linter.deprecated false in
/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists.

See `List.drop_sum_flatten` for the corresponding statement using `List.sum`. -/
@[deprecated "Use `List.drop_sum_flatten`." (since := "2024-10-17")]
theorem drop_sum_flatten' (L : List (List α)) (i : ℕ) :
    L.flatten.drop (Nat.sum ((L.map length).take i)) = (L.drop i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [drop_append, *]

@[deprecated (since := "2024-10-25")] alias drop_sum_join' := drop_sum_flatten'

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_getElem (L : List α) (i : Nat) (h : i < L.length) :
    (L.take (i + 1)).drop i = [L[i]] := by
  induction' L with head tail ih generalizing i
  · exact (Nat.not_succ_le_zero i h).elim
  rcases i with _ | i
  · simp
  · simpa using ih _ (by simpa using h)

set_option linter.deprecated false in
/-- In a flatten of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`.

See `List.drop_take_succ_flatten_eq_getElem` for the corresponding statement using `List.sum`. -/
@[deprecated "Use `List.drop_take_succ_flatten_eq_getElem`." (since := "2024-10-17")]
theorem drop_take_succ_flatten_eq_getElem' (L : List (List α)) (i : Nat) (h : i <  L.length) :
    (L.flatten.take (Nat.sum ((L.map length).take (i + 1)))).drop
      (Nat.sum ((L.map length).take i)) = L[i] := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, length_map, take_sum_flatten', drop_sum_flatten',
    drop_take_succ_eq_cons_getElem, h, flatten, append_nil]

theorem flatten_drop_length_sub_one {L : List (List α)} (h : L ≠ []) :
    (L.drop (L.length - 1)).flatten = L.getLast h := by
  induction L using List.reverseRecOn
  · cases h rfl
  · simp

/-- We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`. -/
theorem append_flatten_map_append (L : List (List α)) (x : List α) :
    x ++ (L.map (· ++ x)).flatten = (L.map (x ++ ·)).flatten ++ x := by
  induction L with
  | nil => rw [map_nil, flatten, append_nil, map_nil, flatten, nil_append]
  | cons _ _ ih =>
    rw [map_cons, flatten, map_cons, flatten, append_assoc, ih, append_assoc, append_assoc]

end List
