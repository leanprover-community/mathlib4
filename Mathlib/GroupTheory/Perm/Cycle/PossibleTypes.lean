/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-! # Possible cycle types of permutations

* For `m : Multiset ℕ`, `Equiv.Perm.exists_with_cycleType_iff m`
  proves that there are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2.

-/

variable (α : Type*) [DecidableEq α] [Fintype α]

/-- There are permutations with cycleType `m` if and only if
  its sum is at most `Fintype.card α` and its members are at least 2. -/
theorem Equiv.Perm.exists_with_cycleType_iff {m : Multiset ℕ} :
    (∃ g : Equiv.Perm α, g.cycleType = m) ↔
      (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) := by
  constructor
  · -- empty case
    intro h
    obtain ⟨g, hg⟩ := h
    constructor
    · rw [← hg, Equiv.Perm.sum_cycleType]
      exact (Equiv.Perm.support g).card_le_univ
    · intro a
      rw [← hg]
      exact Equiv.Perm.two_le_of_mem_cycleType
  · rintro ⟨hc, h2c⟩
    have hc' : m.toList.sum ≤ Fintype.card α := by
      simp only [Multiset.sum_toList]
      exact hc
    obtain ⟨p, hp_length, hp_nodup, hp_disj⟩ := List.exists_pw_disjoint_with_card hc'
    use List.prod (List.map (fun l => List.formPerm l) p)
    have hp2 : ∀ x ∈ p, 2 ≤ x.length := by
      intro x hx
      apply h2c x.length
      rw [← Multiset.mem_toList, ← hp_length, List.mem_map]
      exact ⟨x, hx, rfl⟩
    rw [Equiv.Perm.cycleType_eq _ rfl]
    · -- lengths
      rw [← Multiset.coe_toList m]
      apply congr_arg
      rw [List.map_map]; rw [← hp_length]
      apply List.map_congr_left
      intro x hx; simp only [Function.comp_apply]
      rw [List.support_formPerm_of_nodup x (hp_nodup x hx)]
      ·-- length
        rw [List.toFinset_card_of_nodup (hp_nodup x hx)]
      · -- length >= 1
        intro a h
        apply Nat.not_succ_le_self 1
        conv_rhs => rw [← List.length_singleton a]; rw [← h]
        exact hp2 x hx
    · -- cycles
      intro g
      rw [List.mem_map]
      rintro ⟨x, hx, rfl⟩
      have hx_nodup : x.Nodup := hp_nodup x hx
      rw [← Cycle.formPerm_coe x hx_nodup]
      apply Cycle.isCycle_formPerm
      rw [Cycle.nontrivial_coe_nodup_iff hx_nodup]
      exact hp2 x hx
    · -- disjoint
      rw [List.pairwise_map]
      apply List.Pairwise.imp_of_mem _ hp_disj
      intro a b ha hb hab
      rw [List.formPerm_disjoint_iff (hp_nodup a ha) (hp_nodup b hb) (hp2 a ha) (hp2 b hb)]
      exact hab
