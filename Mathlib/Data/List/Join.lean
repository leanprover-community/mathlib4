/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro, Martin Dvorak
-/
import Mathlib.Data.List.Basic

#align_import data.list.join from "leanprover-community/mathlib"@"18a5306c091183ac90884daa9373fa3b178e8607"

/-!
# Join of a list of lists

This file proves basic properties of `List.join`, which concatenates a list of lists. It is defined
in `Init.Data.List.Basic`.
-/

-- Make sure we don't import algebra
assert_not_exists Monoid

variable {α β : Type*}

namespace List

attribute [simp] join

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem join_singleton (l : List α) : [l].join = l := by rw [join, join, append_nil]
#align list.join_singleton List.join_singleton

@[simp]
theorem join_eq_nil : ∀ {L : List (List α)}, join L = [] ↔ ∀ l ∈ L, l = []
  | [] => iff_of_true rfl (forall_mem_nil _)
  | l :: L => by simp only [join, append_eq_nil, join_eq_nil, forall_mem_cons]
#align list.join_eq_nil List.join_eq_nil

@[simp]
theorem join_append (L₁ L₂ : List (List α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ := by
  induction L₁
  · rfl
  · simp [*]
#align list.join_append List.join_append

theorem join_concat (L : List (List α)) (l : List α) : join (L.concat l) = join L ++ l := by simp
#align list.join_concat List.join_concat

@[simp]
theorem join_filter_not_isEmpty  :
    ∀ {L : List (List α)}, join (L.filter fun l => !l.isEmpty) = L.join
  | [] => rfl
  | [] :: L => by
      simp [join_filter_not_isEmpty (L := L), isEmpty_iff_eq_nil]
  | (a :: l) :: L => by
      simp [join_filter_not_isEmpty (L := L)]
#align list.join_filter_empty_eq_ff List.join_filter_not_isEmpty

@[deprecated (since := "2024-02-25")] alias join_filter_isEmpty_eq_false := join_filter_not_isEmpty

@[simp]
theorem join_filter_ne_nil [DecidablePred fun l : List α => l ≠ []] {L : List (List α)} :
    join (L.filter fun l => l ≠ []) = L.join := by
  simp [join_filter_not_isEmpty, ← isEmpty_iff_eq_nil]
#align list.join_filter_ne_nil List.join_filter_ne_nil

theorem join_join (l : List (List (List α))) : l.join.join = (l.map join).join := by
  induction l <;> simp [*]
#align list.join_join List.join_join

/-- See `List.length_join` for the corresponding statement using `List.sum`. -/
lemma length_join' (L : List (List α)) : length (join L) = Nat.sum (map length L) := by
  induction L <;> [rfl; simp only [*, join, map, Nat.sum_cons, length_append]]

/-- See `List.countP_join` for the corresponding statement using `List.sum`. -/
lemma countP_join' (p : α → Bool) :
    ∀ L : List (List α), countP p L.join = Nat.sum (L.map (countP p))
  | [] => rfl
  | a :: l => by rw [join, countP_append, map_cons, Nat.sum_cons, countP_join' _ l]

/-- See `List.count_join` for the corresponding statement using `List.sum`. -/
lemma count_join' [BEq α] (L : List (List α)) (a : α) :
    L.join.count a = Nat.sum (L.map (count a)) := countP_join' _ _

/-- See `List.length_bind` for the corresponding statement using `List.sum`. -/
lemma length_bind' (l : List α) (f : α → List β) :
    length (l.bind f) = Nat.sum (map (length ∘ f) l) := by rw [List.bind, length_join', map_map]

/-- See `List.countP_bind` for the corresponding statement using `List.sum`. -/
lemma countP_bind' (p : β → Bool) (l : List α) (f : α → List β) :
    countP p (l.bind f) = Nat.sum (map (countP p ∘ f) l) := by rw [List.bind, countP_join', map_map]

/-- See `List.count_bind` for the corresponding statement using `List.sum`. -/
lemma count_bind' [BEq β] (l : List α) (f : α → List β) (x : β) :
    count x (l.bind f) = Nat.sum (map (count x ∘ f) l) := countP_bind' _ _ _

@[simp]
theorem bind_eq_nil {l : List α} {f : α → List β} : List.bind l f = [] ↔ ∀ x ∈ l, f x = [] :=
  join_eq_nil.trans <| by
    simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
#align list.bind_eq_nil List.bind_eq_nil

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists.

See `List.take_sum_join` for the corresponding statement using `List.sum`. -/
theorem take_sum_join' (L : List (List α)) (i : ℕ) :
    L.join.take (Nat.sum ((L.map length).take i)) = (L.take i).join := by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_append, *]

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists.

See `List.drop_sum_join` for the corresponding statement using `List.sum`. -/
theorem drop_sum_join' (L : List (List α)) (i : ℕ) :
    L.join.drop (Nat.sum ((L.map length).take i)) = (L.drop i).join := by
  induction L generalizing i
  · simp
  · cases i <;> simp [drop_append, *]

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_get (L : List α) (i : Fin L.length) :
    (L.take (i + 1)).drop i = [get L i] := by
  induction' L with head tail ih
  · exact (Nat.not_succ_le_zero i i.isLt).elim
  rcases i with ⟨_ | i, hi⟩
  · simp
  · simpa using ih ⟨i, Nat.lt_of_succ_lt_succ hi⟩

set_option linter.deprecated false in
/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
@[deprecated drop_take_succ_eq_cons_get (since := "2023-01-10")]
theorem drop_take_succ_eq_cons_nthLe (L : List α) {i : ℕ} (hi : i < L.length) :
    (L.take (i + 1)).drop i = [nthLe L i hi] := by
  induction' L with head tail generalizing i
  · simp only [length] at hi
    exact (Nat.not_succ_le_zero i hi).elim
  cases' i with i hi
  · simp
    rfl
  have : i < tail.length := by simpa using hi
  simp [*]
  rfl
#align list.drop_take_succ_eq_cons_nth_le List.drop_take_succ_eq_cons_nthLe

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`.

See `List.drop_take_succ_join_eq_get` for the corresponding statement using `List.sum`. -/
theorem drop_take_succ_join_eq_get' (L : List (List α)) (i : Fin L.length) :
    (L.join.take (Nat.sum ((L.map length).take (i + 1)))).drop (Nat.sum ((L.map length).take i)) =
      get L i := by
  have : (L.map length).take i = ((L.take (i + 1)).map length).take i := by
    simp [map_take, take_take, Nat.min_eq_left]
  simp only [this, length_map, take_sum_join', drop_sum_join', drop_take_succ_eq_cons_get,
    join, append_nil]

#noalign list.drop_take_succ_join_eq_nth_le
#noalign list.sum_take_map_length_lt1
#noalign list.sum_take_map_length_lt2
#noalign list.nth_le_join

/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq (L L' : List (List α)) :
    L = L' ↔ L.join = L'.join ∧ map length L = map length L' := by
  refine ⟨fun H => by simp [H], ?_⟩
  rintro ⟨join_eq, length_eq⟩
  apply ext_get
  · have : length (map length L) = length (map length L') := by rw [length_eq]
    simpa using this
  · intro n h₁ h₂
    rw [← drop_take_succ_join_eq_get', ← drop_take_succ_join_eq_get', join_eq, length_eq]
#align list.eq_iff_join_eq List.eq_iff_join_eq

theorem join_drop_length_sub_one {L : List (List α)} (h : L ≠ []) :
    (L.drop (L.length - 1)).join = L.getLast h := by
  induction L using List.reverseRecOn
  · cases h rfl
  · simp
#align list.join_drop_length_sub_one List.join_drop_length_sub_one

/-- We can rebracket `x ++ (l₁ ++ x) ++ (l₂ ++ x) ++ ... ++ (lₙ ++ x)` to
`(x ++ l₁) ++ (x ++ l₂) ++ ... ++ (x ++ lₙ) ++ x` where `L = [l₁, l₂, ..., lₙ]`. -/
theorem append_join_map_append (L : List (List α)) (x : List α) :
    x ++ (L.map (· ++ x)).join = (L.map (x ++ ·)).join ++ x := by
  induction' L with _ _ ih
  · rw [map_nil, join, append_nil, map_nil, join, nil_append]
  · rw [map_cons, join, map_cons, join, append_assoc, ih, append_assoc, append_assoc]
#align list.append_join_map_append List.append_join_map_append

/-- Reversing a join is the same as reversing the order of parts and reversing all parts. -/
theorem reverse_join (L : List (List α)) :
    L.join.reverse = (L.map reverse).reverse.join := by
  induction' L with _ _ ih
  · rfl
  · rw [join, reverse_append, ih, map_cons, reverse_cons', join_concat]
#align list.reverse_join List.reverse_join

/-- Joining a reverse is the same as reversing all parts and reversing the joined result. -/
theorem join_reverse (L : List (List α)) :
    L.reverse.join = (L.map reverse).join.reverse := by
  simpa [reverse_reverse, map_reverse] using congr_arg List.reverse (reverse_join L.reverse)
#align list.join_reverse List.join_reverse

/-- Any member of `L : List (List α))` is a sublist of `L.join` -/
lemma sublist_join (L : List (List α)) {s : List α} (hs : s ∈ L) :
    s.Sublist L.join := by
  induction L with
  | nil =>
    exfalso
    exact not_mem_nil s hs
  | cons t m ht =>
    cases mem_cons.mp hs with
    | inl h =>
      rw [h]
      simp only [join_cons, sublist_append_left]
    | inr h =>
      simp only [join_cons]
      exact sublist_append_of_sublist_right (ht h)

end List
