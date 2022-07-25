/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# Pairwise relations on a List
This file provides basic results about `List.pairwise` and `List.pwFilter` (definitions are in
`data.List.defs`).
`pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`pairwise (≠) l` means that all elements of `l` are distinct, and `pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter r l` is the List obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the List we have so far. It thus yields `l'` a maximal subList of `l` such that
`pairwise r l'`.
## Tags
sorted, nodup
-/

open Nat

namespace List
variable {α : Type _} {R : α → α → Prop} {a : α} {l : List α}

theorem Pairwise_singleton (R) (a : α) : Pairwise R [a] :=
by simp [Pairwise_cons, Pairwise.nil]

variable [DecidableRel R]

@[simp] theorem pwFilter_nil : pwFilter R [] = [] := rfl

@[simp] theorem pwFilter_cons_of_pos {a : α} {l : List α} (h : ∀ b ∈ pwFilter R l, R a b) :
  pwFilter R (a :: l) = a :: pwFilter R l := if_pos h

@[simp] theorem pwFilter_cons_of_neg {a : α} {l : List α} (h : ¬ ∀ b ∈ pwFilter R l, R a b) :
  pwFilter R (a :: l) = pwFilter R l := if_neg h

theorem pwFilter_subset {l : List α} : ∀ (a : α), a ∈ pwFilter R l → a ∈ l := by
  intro a ha
  induction l with
  | nil => rwa [pwFilter_nil] at ha
  | cons x l ih => sorry

theorem pairwise_pwFilter : ∀ (l : List α), Pairwise R (pwFilter R l)
| []     => Pairwise.nil
| x :: l => by
  by_cases (∀ y ∈ pwFilter R l, R x y)
  · rw [pwFilter_cons_of_pos h]
    exact Pairwise_cons.2 ⟨h, pairwise_pwFilter l⟩
  · rw [pwFilter_cons_of_neg h]
    exact pairwise_pwFilter l

theorem pwFilter_eq_self {l : List α} : pwFilter R l = l ↔ Pairwise R l := by
  constructor
  · exact λ e => e ▸ pairwise_pwFilter l
  · intro p
    induction l with
    | nil => rfl
    | cons x l ih =>
      have ⟨ha, hl⟩ := Pairwise_cons.1 p
      conv => rhs; rw [← ih hl]
      exact pwFilter_cons_of_pos λ b hb => ha b (pwFilter_subset b hb)

@[reducible] theorem Pairwise.pwFilter : Pairwise R l → pwFilter R l = l :=
  pwFilter_eq_self.2
