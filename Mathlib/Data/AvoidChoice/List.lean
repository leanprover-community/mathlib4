/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Batteries.Data.List.Lemmas

/-!
# Let's avoid choice!

We gather results that are used to avoid the axiom of choice.

-/

@[expose] public section

open List

universe u
namespace Constructive

namespace List

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    Pairwise (· < ·) (range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := mem_range'.1 m
      calc s < s + step := Nat.lt_add_of_pos_right pos
           _ ≤ s + step + step * a := Nat.le_add_right _ _
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) : Pairwise (· ≤ ·) (range' s n step) :=
  match s, n, step with
  | _, 0, _ => Pairwise.nil
  | s, n + 1, step => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      obtain ⟨a, -, rfl⟩ := mem_range'.1 m
      rw [Nat.add_assoc]
      exact Nat.le_add_right s (step + step * a)
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem nodup_range {n : Nat} : Nodup (range n) := by
  simp +decide only [range_eq_range', nodup_range']

theorem nodup_finRange (n) : (finRange n).Nodup := by
  rw [finRange_eq_pmap_range]
  exact (Pairwise.pmap nodup_range _) fun _ _ _ _ => @Fin.ne_of_val_ne _ ⟨_, _⟩ ⟨_, _⟩

theorem eq_nil_iff_forall_not_mem {α : Type u} {l : List α} : l = [] ↔ ∀ a, a ∉ l := by
  cases l <;> simp [-not_or]

end List

end Constructive
