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

section Ranges

/-- For any `c : List ℕ` whose sum is at most `Fintype.card α`,
  we can find `o : List (List α)` whose members have no duplicate,
  whose lengths given by `c`, and which are pairwise disjoint -/
theorem List.exists_pw_disjoint_with_card {α : Type*} [Fintype α]
    {c : List ℕ} (hc : c.sum ≤ Fintype.card α) :
    ∃ o : List (List α),
      o.map length = c ∧ (∀ s ∈ o, s.Nodup) ∧ Pairwise List.Disjoint o := by
  let klift (n : ℕ) (hn : n < Fintype.card α) : Fin (Fintype.card α) :=
    (⟨n, hn⟩ : Fin (Fintype.card α))
  let klift' (l : List ℕ) (hl : ∀ a ∈ l, a < Fintype.card α) :
    List (Fin (Fintype.card α)) := List.pmap klift l hl
  have hc'_lt : ∀ l ∈ c.ranges, ∀ n ∈ l, n < Fintype.card α := by
    intro l hl n hn
    apply lt_of_lt_of_le _ hc
    rw [← mem_mem_ranges_iff_lt_sum]
    exact ⟨l, hl, hn⟩
  let l := (ranges c).pmap klift' hc'_lt
  have hl : ∀ (a : List ℕ) (ha : a ∈ c.ranges),
    (klift' a (hc'_lt a ha)).map Fin.valEmbedding = a := by
    intro a ha
    conv_rhs => rw [← List.map_id a]
    rw [List.map_pmap]
    simp [klift, Fin.valEmbedding_apply, Fin.val_mk, List.pmap_eq_map, List.map_id']
  use l.map (List.map (Fintype.equivFin α).symm)
  constructor
  · -- length
    rw [← ranges_length c]
    simp only [l, klift', map_map, map_pmap, Function.comp_apply, length_map, length_pmap,
      pmap_eq_map]
  constructor
  · -- nodup
    intro s
    rw [mem_map]
    rintro ⟨t, ht, rfl⟩
    apply Nodup.map (Equiv.injective _)
    obtain ⟨u, hu, rfl⟩ := mem_pmap.mp ht
    apply Nodup.of_map
    rw [hl u hu]
    exact ranges_nodup hu
  · -- pairwise disjoint
    refine Pairwise.map _ (fun s t ↦ disjoint_map (Equiv.injective _)) ?_
    -- List.Pairwise List.disjoint l
    apply Pairwise.pmap (List.ranges_disjoint c)
    intro u hu v hv huv
    apply disjoint_pmap
    · intro a a' ha ha' h
      simpa only [klift, Fin.mk_eq_mk] using h
    exact huv

end Ranges

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
        conv_rhs => rw [← List.length_singleton (a := a)]; rw [← h]
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
