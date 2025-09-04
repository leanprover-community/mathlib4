/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Anthony DeRossi
-/
import Mathlib.Data.List.Basic

/-!
# Properties of `List.reduceOption`

In this file we prove basic lemmas about `List.reduceOption`.
-/

namespace List

variable {α β : Type*}

@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id]

@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id]

@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl

@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  · simp only [reduceOption_nil, map_nil]
  · cases hd <;>
      simpa [Option.map_some, map, eq_self_iff_true, reduceOption_cons_of_some] using hl

theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append

@[simp]
theorem reduceOption_replicate_none {n : ℕ} : (replicate n (@none α)).reduceOption = [] := by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none (id_def _)]

theorem reduceOption_eq_nil_iff (l : List (Option α)) :
    l.reduceOption = [] ↔ ∃ n, l = replicate n none := by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · intro ⟨_, h⟩
    simp_rw [h, mem_replicate]
    tauto

theorem reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) :
    l.reduceOption = [a] ↔ ∃ m n, l = replicate m none ++ some a :: replicate n none := by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_cons_iff] at h
    obtain ⟨l₁, _, l₂, h, hl₁, ⟨⟩, hl₂⟩ := h
    rw [filterMap_eq_nil_iff] at hl₂
    apply eq_replicate_of_mem at hl₁
    apply eq_replicate_of_mem at hl₂
    rw [h, hl₁, hl₂]
    use l₁.length, l₂.length
  · intro ⟨_, _, h⟩
    simp only [h, filterMap_append, filterMap_cons_some, filterMap_replicate_of_none, id_eq,
      nil_append, Option.some.injEq]

theorem reduceOption_eq_append_iff (l : List (Option α)) (l'₁ l'₂ : List α) :
    l.reduceOption = l'₁ ++ l'₂ ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l'₁ ∧ l₂.reduceOption = l'₂ := by
  dsimp [reduceOption]
  exact filterMap_eq_append_iff

theorem reduceOption_eq_concat_iff (l : List (Option α)) (l' : List α) (a : α) :
    l.reduceOption = l'.concat a ↔
      ∃ l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = [] := by
  rw [concat_eq_append]
  constructor
  · intro h
    rw [reduceOption_eq_append_iff] at h
    obtain ⟨l₁, _, h, hl₁, hl₂⟩ := h
    rw [reduceOption_eq_singleton_iff] at hl₂
    obtain ⟨m, n, hl₂⟩ := hl₂
    use l₁ ++ replicate m none, replicate n none
    simp_rw [h, reduceOption_append, reduceOption_replicate_none, append_assoc, append_nil, hl₁,
      hl₂, and_self]
  · intro ⟨_, _, h, hl₁, hl₂⟩
    rw [h, reduceOption_append, reduceOption_cons_of_some, hl₁, hl₂]

theorem reduceOption_length_eq {l : List (Option α)} :
    l.reduceOption.length = (l.filter Option.isSome).length := by
  induction' l with hd tl hl
  · simp_rw [reduceOption_nil, filter_nil, length]
  · cases hd <;> simp [hl]

theorem length_eq_reduceOption_length_add_filter_none {l : List (Option α)} :
    l.length = l.reduceOption.length + (l.filter Option.isNone).length := by
  simp_rw [reduceOption_length_eq, l.length_eq_length_filter_add Option.isSome, Option.not_isSome]

theorem reduceOption_length_le (l : List (Option α)) : l.reduceOption.length ≤ l.length := by
  rw [length_eq_reduceOption_length_add_filter_none]
  apply Nat.le_add_right

theorem reduceOption_length_eq_iff {l : List (Option α)} :
    l.reduceOption.length = l.length ↔ ∀ x ∈ l, Option.isSome x := by
  rw [reduceOption_length_eq, List.length_filter_eq_length_iff]

theorem reduceOption_length_lt_iff {l : List (Option α)} :
    l.reduceOption.length < l.length ↔ none ∈ l := by
  rw [Nat.lt_iff_le_and_ne, and_iff_right (reduceOption_length_le l), Ne,
    reduceOption_length_eq_iff]
  induction l
  · simp
  · grind [cases Option]

theorem reduceOption_singleton (x : Option α) : [x].reduceOption = x.toList := by cases x <;> rfl

theorem reduceOption_concat (l : List (Option α)) (x : Option α) :
    (l.concat x).reduceOption = l.reduceOption ++ x.toList := by
  induction' l with hd tl hl generalizing x
  · cases x <;> simp [Option.toList]
  · simp only [concat_eq_append, reduceOption_append] at hl
    cases hd <;> simp [hl, reduceOption_append]

theorem reduceOption_concat_of_some (l : List (Option α)) (x : α) :
    (l.concat (some x)).reduceOption = l.reduceOption.concat x := by
  simp only [reduceOption_nil, concat_eq_append, reduceOption_append, reduceOption_cons_of_some]

theorem reduceOption_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduceOption ↔ some x ∈ l := by
  simp only [reduceOption, id, mem_filterMap, exists_eq_right]

theorem reduceOption_getElem?_iff {l : List (Option α)} {x : α} :
    (∃ i : ℕ, l[i]? = some (some x)) ↔ ∃ i : ℕ, l.reduceOption[i]? = some x := by
  rw [← mem_iff_getElem?, ← mem_iff_getElem?, reduceOption_mem_iff]

end List
