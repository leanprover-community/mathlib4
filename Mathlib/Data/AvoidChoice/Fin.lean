/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

import Batteries.Data.List.Lemmas
import Mathlib.Algebra.Order.Group.Nat

/-!
# Let's avoid choice!

We gather results that are used to avoid the axiom of choice.

-/

@[expose] public section

namespace Constructive

namespace List

open List

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    List.Pairwise (· < ·) (List.range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => List.Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [List.range'_succ, List.pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := List.mem_range'.1 m
      calc s < s + step := lt_add_of_pos_right _ pos
           _ ≤ s + step + step * a := Nat.le_add_right _ _
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) :
    List.Pairwise (· ≤ ·) (List.range' s n step) :=
  match s, n, step with
  | _, 0, _ => List.Pairwise.nil
  | s, n + 1, step => by
    simp only [List.range'_succ, List.pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := List.mem_range'.1 m
      rw [add_assoc]
      exact Nat.le_add_right s (step + step * a)
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) :
    List.Nodup (List.range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem nodup_range {n : Nat} : List.Nodup (List.range n) := by
  simp +decide only [List.range_eq_range', nodup_range']

theorem nodup_finRange (n) : (List.finRange n).Nodup := by
  rw [List.finRange_eq_pmap_range]
  exact (List.Pairwise.pmap nodup_range _) fun _ _ _ _ => @Fin.ne_of_val_ne _ ⟨_, _⟩ ⟨_, _⟩

end List

end Constructive
