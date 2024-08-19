/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

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

section CountP

variable (p q : α → Bool)

theorem length_filter_lt_length_iff_exists (l) :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  simpa [length_eq_countP_add_countP p l, countP_eq_length_filter] using
  countP_pos (fun x => ¬p x) (l := l)

-- Porting note: `Lean.Internal.coeM` forces us to type-ascript `{x // x ∈ l}`
lemma countP_attach (l : List α) : l.attach.countP (fun a : {x // x ∈ l} ↦ p a) = l.countP p := by
  simp_rw [← Function.comp_apply (g := Subtype.val), ← countP_map, attach_map_val]

end CountP

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

@[simp]
lemma count_attach (a : {x // x ∈ l}) : l.attach.count a = l.count ↑a :=
  Eq.trans (countP_congr fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _

end Count

end List
