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

universe u

variable {V : Type u} {r : V → V → Prop}

/-- Convert an equivalence class to a Set -/
def Quot.toSet (c : Quot r) : Set V := {v | Quot.mk r v = c}

instance : SetLike (Quot r) V where
  coe := Quot.toSet
  coe_injective' := by
    intro x y h
    simp only [Quot.toSet] at h
    simpa using show x.out ∈ {v | Quot.mk r v = y} from by
      rw [← h]
      exact Quot.out_eq x

namespace Set

/-- A set represents a set of quotients if it contains exactly one element from each quotient. -/
structure Represents (s : Set V) (C : Set (Quot r)) where
  unique_rep {c : Quot r} (h : c ∈ C) : ∃! v, v ∈ s ∩ c
  exact {c : Quot r} (h : c ∉ C) : s ∩ c = ∅

lemma represents_of_image_exists_rep_choose (C : Set (Quot r)) :
    ((fun c ↦ c.out) '' C).Represents C where
  unique_rep {c} h := by
    use c.out
    simp only [Set.mem_inter_iff, and_imp]
    refine ⟨⟨by aesop, Quot.out_eq _⟩, ?_⟩
    intro y hy hyc
    obtain ⟨c', ⟨_, rfl⟩⟩ := hy
    rw [← hyc, show Quot.mk r (Quot.out c') = c'
      from Quot.out_eq c']
  exact {c} {h} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false,
      not_and, forall_exists_index, and_imp]
    intro c' hc' hv hvc
    have : c = c' := by
      rw [← hvc, ← hv]
      exact (Quot.exists_rep c').choose_spec
    exact h (this ▸ hc')

lemma ncard_represents_inter {C : Set (Quot r)} {s : Set V}
    {c : (Quot r)} (hrep : s.Represents C) (h : c ∈ C) : (s ∩ c).ncard = 1 := by
  rw [Set.ncard_eq_one]
  obtain ⟨a, ha⟩ := hrep.unique_rep h
  aesop

lemma disjoint_represents {C : Set (Quot r)} {s : Set V}
    {c : (Quot r)} (hrep : s.Represents C) (h : c ∉ C) : Disjoint s c := by
  rw [Set.disjoint_right]
  intro v hv hvr
  have := hrep.exact h
  rw [Set.eq_empty_iff_forall_not_mem] at this
  simp_all

lemma disjoint_of_represents {c : Quot r}
    {s : Set V} {p : (Quot r) → Prop}
    (hrep : s.Represents {c | p c})
    (h : ¬ p c) : Disjoint s c := by
  apply disjoint_represents hrep
  simp_all only [Set.mem_setOf_eq, not_false_eq_true]

lemma ncard_sdiff_represents_of_mem [Fintype V] {c : Quot r}
    {s : Set V} {C : Set (Quot r)}
    (hrep : s.Represents C) (h : c ∈ C) : ((c : Set V) \ s).ncard = (c : Set V).ncard - 1 := by
  simp [← Set.ncard_inter_add_ncard_diff_eq_ncard c s (Set.toFinite _),
    Set.inter_comm, ncard_represents_inter hrep h]

lemma ncard_sdiff_represents_of_not_mem [Fintype V] {c : Quot r}
    {s : Set V} {C : Set (Quot r)}
    (hrep : s.Represents C) (h : c ∉ C) : ((c : Set V) \ s).ncard = (c : Set V).ncard := by
  simp [← Set.ncard_inter_add_ncard_diff_eq_ncard c s (Set.toFinite _),
    Set.inter_comm, hrep.exact h]

end Set
