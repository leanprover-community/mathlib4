/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Tactic.Cases
import Mathlib.Tactic.TypeStar

/-!
# Properties of `List.reduceOption`

In this file we prove basic lemmas about `List.reduceOption`.
-/

namespace List

variable {α β : Type*}

@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id, eq_self_iff_true, and_self_iff]
#align list.reduce_option_cons_of_some List.reduceOption_cons_of_some

@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id]
#align list.reduce_option_cons_of_none List.reduceOption_cons_of_none

@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl
#align list.reduce_option_nil List.reduceOption_nil

@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  · simp only [reduceOption_nil, map_nil]
  · cases hd <;>
      simpa [true_and_iff, Option.map_some', map, eq_self_iff_true,
        reduceOption_cons_of_some] using hl
#align list.reduce_option_map List.reduceOption_map

theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append l l' id
#align list.reduce_option_append List.reduceOption_append

theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length := by
  induction' l with hd tl hl
  · simp [reduceOption_nil, length]
  · cases hd
    · exact Nat.le_succ_of_le hl
    · simpa only [length, Nat.add_le_add_iff_right, reduceOption_cons_of_some] using hl
#align list.reduce_option_length_le List.reduceOption_length_le

theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x := by
  induction' l with hd tl hl
  · simp only [forall_const, reduceOption_nil, not_mem_nil, forall_prop_of_false, eq_self_iff_true,
      length, not_false_iff]
  · cases hd
    · simp only [mem_cons, forall_eq_or_imp, Bool.coe_sort_false, false_and_iff,
        reduceOption_cons_of_none, length, Option.isSome_none, iff_false_iff]
      intro H
      have := reduceOption_length_le tl
      rw [H] at this
      exact absurd (Nat.lt_succ_self _) (Nat.not_lt_of_le this)
    · simp only [length, mem_cons, forall_eq_or_imp, Option.isSome_some, ← hl, reduceOption,
        true_and]
      omega
#align list.reduce_option_length_eq_iff List.reduceOption_length_eq_iff

theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l := by
  rw [Nat.lt_iff_le_and_ne, and_iff_right (reduceOption_length_le l), Ne,
    reduceOption_length_eq_iff]
  induction l <;> simp [*]
  rw [@eq_comm _ none, ← Option.not_isSome_iff_eq_none, Decidable.imp_iff_not_or]
#align list.reduce_option_length_lt_iff List.reduceOption_length_lt_iff

theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl
#align list.reduce_option_singleton List.reduceOption_singleton

theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction' l with hd tl hl generalizing x
  · cases x <;> simp [Option.toList]
  · simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]
#align list.reduce_option_concat List.reduceOption_concat

theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]
#align list.reduce_option_concat_of_some List.reduceOption_concat_of_some

theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduceOption, id, mem_filterMap, exists_eq_right]
#align list.reduce_option_mem_iff List.reduceOption_mem_iff

theorem reduceOption_get?_iff {l : List (Option α)} {x : α} :
    (∃ i, l.get? i = some (some x)) ↔ ∃ i, l.reduceOption.get? i = some x := by
  rw [← mem_iff_get?, ← mem_iff_get?, reduceOption_mem_iff]
#align list.reduce_option_nth_iff List.reduceOption_get?_iff
