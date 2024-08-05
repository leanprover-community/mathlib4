/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.Nat.Defs

/-!
# Counting in lists

This file proves basic properties of `List.countP` and `List.count`, which count the number of
elements of a list satisfying a predicate and equal to a given element respectively. Their
definitions can be found in `Batteries.Data.List.Basic`.
-/

assert_not_exists Set.range
assert_not_exists GroupWithZero
assert_not_exists Ring

open Nat

variable {α : Type*} {l : List α}

namespace List

/-! ### count -/

section Count

@[simp]
theorem count_map_of_injective {β} [DecidableEq α] [DecidableEq β] (l : List α) (f : α → β)
    (hf : Function.Injective f) (x : α) : count (f x) (map f l) = count x l := by
  simp only [count, countP_map, (· ∘ ·), hf.beq_eq]

variable [DecidableEq α]

@[deprecated (since := "2023-08-23")]
theorem count_cons' (a b : α) (l : List α) :
    count a (b :: l) = count a l + if a = b then 1 else 0 := by
  simp only [count, beq_iff_eq, countP_cons, Nat.add_right_inj]
  simp only [eq_comm]

end Count

end List
