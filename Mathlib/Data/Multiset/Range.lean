/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Range

#align_import data.multiset.range from "leanprover-community/mathlib"@"0a0ec35061ed9960bf0e7ffb0335f44447b58977"

/-! # `Multiset.range n` gives `{0, 1, ..., n-1}` as a multiset. -/


open List Nat

namespace Multiset

-- range
/-- `range n` is the multiset lifted from the list `range n`,
  that is, the set `{0, 1, ..., n-1}`. -/
def range (n : ℕ) : Multiset ℕ :=
  List.range n
#align multiset.range Multiset.range

theorem coe_range (n : ℕ) : ↑(List.range n) = range n :=
  rfl
#align multiset.coe_range Multiset.coe_range

@[simp]
theorem range_zero : range 0 = 0 :=
  rfl
#align multiset.range_zero Multiset.range_zero

@[simp]
theorem range_succ (n : ℕ) : range (succ n) = n ::ₘ range n := by
  rw [range, List.range_succ, ← coe_add, add_comm]; rfl
  -- ⊢ ↑[n] + ↑(List.range n) = n ::ₘ range n
                                                    -- 🎉 no goals
#align multiset.range_succ Multiset.range_succ

@[simp]
theorem card_range (n : ℕ) : card (range n) = n :=
  length_range _
#align multiset.card_range Multiset.card_range

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
  List.range_subset
#align multiset.range_subset Multiset.range_subset

@[simp]
theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
  List.mem_range
#align multiset.mem_range Multiset.mem_range

--Porting note: removing @[simp], `simp` can prove it
theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
  List.not_mem_range_self
#align multiset.not_mem_range_self Multiset.not_mem_range_self

theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  List.self_mem_range_succ n
#align multiset.self_mem_range_succ Multiset.self_mem_range_succ

theorem range_add (a b : ℕ) : range (a + b) = range a + (range b).map (a + ·) :=
  congr_arg ((↑) : List ℕ → Multiset ℕ) (List.range_add _ _)
#align multiset.range_add Multiset.range_add

theorem range_disjoint_map_add (a : ℕ) (m : Multiset ℕ) :
    (range a).Disjoint (m.map (a + ·)) := by
  intro x hxa hxb
  -- ⊢ False
  rw [range, mem_coe, List.mem_range] at hxa
  -- ⊢ False
  obtain ⟨c, _, rfl⟩ := mem_map.1 hxb
  -- ⊢ False
  exact (self_le_add_right _ _).not_lt hxa
  -- 🎉 no goals
#align multiset.range_disjoint_map_add Multiset.range_disjoint_map_add

theorem range_add_eq_union (a b : ℕ) : range (a + b) = range a ∪ (range b).map (a + ·) := by
  rw [range_add, add_eq_union_iff_disjoint]
  -- ⊢ Disjoint (range a) (map (fun x => a + x) (range b))
  apply range_disjoint_map_add
  -- 🎉 no goals
#align multiset.range_add_eq_union Multiset.range_add_eq_union

end Multiset
