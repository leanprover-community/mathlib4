/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Basic

/-! # `Multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/


open List Nat

namespace Multiset

-- range
/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : Multiset ℕ :=
  List.range n

theorem coe_range (n : ℕ) : ↑(List.range n) = range n :=
  rfl

@[simp]
theorem range_zero : range 0 = 0 :=
  rfl

@[simp]
theorem range_succ (n : ℕ) : range (succ n) = n ::ₘ range n := by
  rw [range, List.range_succ, ← coe_add, add_comm]; rfl

@[simp]
theorem card_range (n : ℕ) : card (range n) = n :=
  length_range _

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
  List.range_subset

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
  List.mem_range

theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  List.not_mem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  List.self_mem_range_succ n

theorem range_add (a b : ℕ) : range (a + b) = range a + (range b).map (a + ·) :=
  congr_arg ((↑) : List ℕ → Multiset ℕ) (List.range_add _ _)

theorem range_disjoint_map_add (a : ℕ) (m : Multiset ℕ) :
    Disjoint (range a) (m.map (a + ·)) := by
  rw [disjoint_left]
  intro x hxa hxb
  rw [range, mem_coe, List.mem_range] at hxa
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  exact (Nat.le_add_right _ _).not_lt hxa

theorem range_add_eq_union (a b : ℕ) : range (a + b) = range a ∪ (range b).map (a + ·) := by
  rw [range_add, add_eq_union_iff_disjoint]
  apply range_disjoint_map_add

end Multiset
