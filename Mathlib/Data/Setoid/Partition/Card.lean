/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Setoid.Partition

/-! # Cardinality of parts of partitions

* `Setoid.IsPartition.ncard_eq_finsum` on an ambient finite type,
  the cardinal of a set is the sum of the cardinalities of its trace on the parts of the partition

-/

section Finite

open scoped BigOperators

/-- Given a partition of the ambient type, the cardinal of a finite set
  is the `finsum` of the cardinalities of its traces on the parts of the partition -/
theorem Setoid.IsPartition.ncard_eq_finsum {α : Type*} {P : Set (Set α)}
    (hP : Setoid.IsPartition P) (s : Set α) (hs : s.Finite := by toFinite_tac) :
    s.ncard = finsum fun t : P => (s ∩ t).ncard := by
  classical
  have hst (t : Set α) : (s ∩ t).Finite := hs.inter_of_left t
  have hst' (t : Set α) : Nat.card ↑(s ∩ t) = (hst t).toFinset.card :=
    Nat.card_eq_card_finite_toFinset (hst t)
  suffices hs' : _ by
    rw [finsum_def, dif_pos hs']
    simp only [← Set.Nat.card_coe_set_eq, Nat.card_eq_card_finite_toFinset hs]
    rw [Finset.sum_congr rfl (fun t ht ↦ by exact hst' ↑t)]
    rw [← Finset.card_sigma, eq_comm]
    apply Finset.card_nbij' (fun ⟨t, x⟩ ↦ x)
      (fun x ↦ ⟨⟨(hP.2 x).exists.choose, (hP.2 x).exists.choose_spec.1⟩, x⟩)
    · rintro ⟨t, x⟩
      simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Set.mem_inter_iff, and_imp]
      exact fun _ a _ ↦ a
    · intro x
      simp only [Set.Finite.mem_toFinset, Finset.mem_sigma, Function.mem_support, Set.mem_inter_iff]
      intro hx
      refine ⟨Nat.card_ne_zero.mpr ⟨?_, hst (hP.right x).exists.choose⟩,
        hx, (hP.2 x).exists.choose_spec.2⟩
      simp only [nonempty_subtype, Set.mem_inter_iff]
      use x, hx, (hP.2 x).exists.choose_spec.2
    · rintro ⟨t, x⟩
      simp only [Finset.mem_sigma, Set.Finite.mem_toFinset, Function.mem_support, Nat.card_ne_zero,
        Set.mem_inter_iff, Sigma.mk.inj_iff, heq_eq_eq, and_true, and_imp]
      simp only [nonempty_subtype, Set.mem_inter_iff, forall_exists_index, and_imp]
      intro y hy hyt _ hxs hxt
      rw [← Subtype.coe_inj]
      exact (hP.2 x).unique (hP.2 x).exists.choose_spec ⟨t.prop, hxt⟩
    · intro t
      simp only [Set.Finite.mem_toFinset, implies_true]
  let f : Function.support (fun (t : P) ↦ (s ∩ (t : Set α)).ncard) → s := fun ⟨t, ht⟩ ↦
    ⟨(Set.nonempty_of_ncard_ne_zero ht).choose, (Set.nonempty_of_ncard_ne_zero ht).choose_spec.1⟩
  have hf (t : Function.support (fun (t : P) ↦ (s ∩ (t : Set α)).ncard)) :
      ↑↑t ∈ P ∧ (f t : α) ∈ (t : Set α) :=
    ⟨(↑t : P).prop, (Set.nonempty_of_ncard_ne_zero t.prop).choose_spec.2⟩
  have : Finite ↑s := hs
  apply Finite.of_injective f
  intro t t' h
  simp only [← Subtype.coe_inj, Subtype.coe_mk]
  exact (hP.2 (f t)).unique (hf t) (h ▸ hf t')

end Finite
