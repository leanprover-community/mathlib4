/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Minimal

/-!
# Maximal upper and minimal lower bounds of elements in finsets

Let a finset over a partially ordered type and an element in it be given, then

* `Finset.exists_maximal_upper_bound` says that it has a maximal upper bound.
* `Finset.exists_minimal_lower_bound` says that it has a minimal lower bound.
-/

namespace Finset

variable {α : Type*} [PartialOrder α] {s : Finset α} {a : α}

/-- Every element in a finset over a partially ordered type has a maximal upper bound. -/
lemma exists_maximal_upper_bound (h : a ∈ s) : ∃ m ≥ a, Maximal (· ∈ s) m := by
  classical let C : Finset α := s.filter (a ≤ ·)
  obtain ⟨m, hm, maxm⟩ := C.exists_maximal ⟨a, by simp [C, h]⟩
  simp_rw [C, mem_filter] at hm maxm
  use m, hm.2; rw [maximal_iff]
  exact ⟨hm.1, fun b mb lb ↦ eq_of_le_of_not_lt lb (maxm b ⟨mb, hm.2.trans lb⟩)⟩

/-- Every element in a finset over a partially ordered type has a minimal lower bound. -/
lemma exists_minimal_lower_bound (h : a ∈ s) : ∃ m ≤ a, Minimal (· ∈ s) m := by
  classical let C : Finset α := s.filter (· ≤ a)
  obtain ⟨m, hm, minm⟩ := C.exists_minimal ⟨a, by simp [C, h]⟩
  simp_rw [C, mem_filter] at hm minm
  use m, hm.2; rw [minimal_iff]
  exact ⟨hm.1, fun b mb ub ↦ (eq_of_le_of_not_lt ub (minm b ⟨mb, ub.trans hm.2⟩)).symm⟩

end Finset
