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
def Quot.toSet (c : Quot r) : Set α := {x | Quot.mk r x = c}

instance : SetLike (Quot r) α where
  coe := Quot.toSet
  coe_injective' x y h := by
    simp only [Quot.toSet] at h
    simpa using show x.out ∈ {v | Quot.mk r v = y} by
      rw [← h]
      exact x.out_eq

@[simp] lemma Quot.mem_toSet {x : α} {c : Quot r} : x ∈ c ↔ Quot.mk r x = c := Iff.rfl

@[ext] theorem Quot.ext (c d : Quot r) (h : ∀ x, x ∈ c ↔ x ∈ d) : c = d := SetLike.ext h

namespace Set

/-- A set represents a set of quotients if it contains exactly one element from each quotient. -/
def Represents (s : Set α) (C : Set (Quot r)) := Set.BijOn (Quot.mk r) s C

lemma out_image_represents (C : Set (Quot r)) : (Quot.out '' C).Represents C :=
  Set.BijOn.mk (by rintro c ⟨x, ⟨hx, rfl⟩⟩; simp_all) (by
    rintro x ⟨c, ⟨hc, rfl⟩⟩ y ⟨d, ⟨hd, rfl⟩⟩ hxy
    aesop) (fun _ _ ↦ by simpa)

namespace Represents

variable {C : Set (Quot r)} {s : Set α} {c : Quot r}

lemma unique_rep (hrep : s.Represents C) (h : c ∈ C) : ∃! x, x ∈ s ∩ c := by
  obtain ⟨x, ⟨hx, rfl⟩⟩ := hrep.2.2 h
  use x
  simp only [mem_inter_iff, hx, SetLike.mem_coe, Quot.mem_toSet, and_self, and_imp, true_and]
  exact fun y hy hyx ↦ hrep.2.1 hy hx hyx

lemma exact (hrep : s.Represents C) (h : c ∉ C) : Disjoint s c := by
  rw [disjoint_left]
  intro a ha hc
  simp only [SetLike.mem_coe, Quot.mem_toSet] at hc
  subst hc
  exact h (hrep.1 ha)

lemma ncard_inter (hrep : s.Represents C) (h : c ∈ C) : (s ∩ c).ncard = 1 := by
  rw [ncard_eq_one]
  obtain ⟨a, ha⟩ := hrep.unique_rep h
  aesop

lemma ncard_sdiff_of_mem [Fintype α] (hrep : s.Represents C) (h : c ∈ C) :
    ((c : Set α) \ s).ncard = (c : Set α).ncard - 1 := by
  simp [← ncard_inter_add_ncard_diff_eq_ncard c s (toFinite _),
    inter_comm, ncard_inter hrep h]

lemma ncard_sdiff_of_not_mem [Fintype α] (hrep : s.Represents C) (h : c ∉ C) :
    ((c : Set α) \ s).ncard = (c : Set α).ncard := by
  simp [← ncard_inter_add_ncard_diff_eq_ncard c s (toFinite _),
    inter_comm, disjoint_iff_inter_eq_empty.mp (hrep.exact h)]

end Represents

end Set
