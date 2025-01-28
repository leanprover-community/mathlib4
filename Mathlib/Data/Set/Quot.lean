/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Data.Set.Card

/-!
# Quotients as Sets

## Main definitions

* `Quot.toSet` interprets an equivalence class as a set.
* `Set.Represents` says that a set represents a set of quotients if it contains exactly one element
  from each quotient.
-/

variable {α : Type*} {r : α → α → Prop}

/-- Convert an equivalence class to a `Set`. -/
def Quot.toSet (c : Quot r) : Set α := {v | Quot.mk r v = c}

instance : SetLike (Quot r) α where
  coe := Quot.toSet
  coe_injective' x y h := by
    simp only [Quot.toSet] at h
    simpa using show x.out ∈ {v | Quot.mk r v = y} by
      rw [← h]
      exact x.out_eq

namespace Set

/-- A set represents a set of quotients if it contains exactly one element from each quotient. -/
structure Represents (s : Set α) (C : Set (Quot r)) where
  unique_rep {c : Quot r} (h : c ∈ C) : ∃! v, v ∈ s ∩ c
  exact {c : Quot r} (h : c ∉ C) : s ∩ c = ∅

lemma out_image_represents (C : Set (Quot r)) : (Quot.out '' C).Represents C where
  unique_rep {c} h := by
    use c.out
    simp only [mem_inter_iff, and_imp]
    refine ⟨⟨by aesop, Quot.out_eq _⟩, fun y hy hyc ↦ ?_⟩
    obtain ⟨c', ⟨_, rfl⟩⟩ := hy
    rw [← hyc, c'.out_eq]
  exact {c} h := by
    ext v
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false,
      not_and, forall_exists_index, and_imp]
    intro c' hc' hv hvc
    rw [← hvc, ← hv, c'.out_eq] at h
    exact h hc'

lemma ncard_represents_inter {C : Set (Quot r)} {s : Set α} {c : (Quot r)} (hrep : s.Represents C)
    (h : c ∈ C) : (s ∩ c).ncard = 1 := by
  rw [ncard_eq_one]
  obtain ⟨a, ha⟩ := hrep.unique_rep h
  aesop

lemma disjoint_represents {C : Set (Quot r)} {s : Set α} {c : Quot r} (hrep : s.Represents C)
    (h : c ∉ C) : Disjoint s c := by
  rw [disjoint_right]
  intro v hv hvr
  have := hrep.exact h
  rw [eq_empty_iff_forall_not_mem] at this
  simp_all

lemma ncard_sdiff_represents_of_mem [Fintype α] {c : Quot r} {s : Set α} {C : Set (Quot r)}
    (hrep : s.Represents C) (h : c ∈ C) : ((c : Set α) \ s).ncard = (c : Set α).ncard - 1 := by
  simp [← ncard_inter_add_ncard_diff_eq_ncard c s (toFinite _),
    inter_comm, ncard_represents_inter hrep h]

lemma ncard_sdiff_represents_of_not_mem [Fintype α] {c : Quot r} {s : Set α} {C : Set (Quot r)}
    (hrep : s.Represents C) (h : c ∉ C) : ((c : Set α) \ s).ncard = (c : Set α).ncard := by
  simp [← ncard_inter_add_ncard_diff_eq_ncard c s (toFinite _),
    inter_comm, hrep.exact h]

end Set
