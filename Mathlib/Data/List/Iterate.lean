/-
Copyright (c) 2024 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/

import Mathlib.Data.List.Defs
import Mathlib.Algebra.Order.Ring.Nat

/-!
# iterate

Proves various lemmas about `List.iterate`.
-/

variable {α : Type*}

namespace List

@[simp]
theorem length_iterate (f : α → α) (a : α) (n : ℕ) : length (iterate f a n) = n := by
  induction n generalizing a <;> simp [*]

@[simp]
theorem iterate_eq_nil {f : α → α} {a : α} {n : ℕ} : iterate f a n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_iterate]

theorem get?_iterate (f : α → α) (a : α) :
    ∀ (n i : ℕ), i < n → get? (iterate f a n) i = f^[i] a
  | n + 1, 0    , _ => rfl
  | n + 1, i + 1, h => by simp [get?_iterate f (f a) n i (by simpa using h)]

@[simp]
theorem get_iterate (f : α → α) (a : α) (n : ℕ) (i : Fin (iterate f a n).length) :
    get (iterate f a n) i = f^[↑i] a :=
  (get?_eq_some.1 <| get?_iterate f a n i.1 (by simpa using i.2)).2

@[simp]
theorem mem_iterate {f : α → α} {a : α} {n : ℕ} {b : α} :
    b ∈ iterate f a n ↔ ∃ m < n, b = f^[m] a := by
  simp [List.mem_iff_get, Fin.exists_iff, eq_comm (b := b)]

@[simp]
theorem range_map_iterate (n : ℕ) (f : α → α) (a : α) :
    (List.range n).map (f^[·] a) = List.iterate f a n := by
  apply List.ext_get <;> simp

end List
