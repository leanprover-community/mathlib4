/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Index


/-! # B. H. Neumann's theorem on coverings of a group by cosets

-/

open scoped Pointwise

variable (G : Type*) [Group G]

variable {ι : Type*} (s : Finset ι)
    (H : ι → Subgroup G) (g : ι → G)
    (covers: ⋃ i ∈ s, (g i) • (H i : Set G) = ⊤)

lemma exists_of_finite_index : ∃ i, 0 < (H i).index := sorry

lemma of_finite_index_covers :
    ⋃ i ∈ s.filter (fun i ↦ (H i).index ≠ 0), (g i) • (H i : Set G) = ⊤ :=
  sorry

theorem BHNeumann_of_subgroup (H : Subgroup G) (g : ι → G)
    (covers : ⋃ i ∈ s, (g i) • (H : Set G) = ⊤) :
    H.index ≤ s.card := by
  cases (H.index).eq_zero_or_pos with
  | inl h => exact h ▸ Nat.zero_le s.card
  | inr h =>
    classical
    haveI : Finite (G ⧸ H) := by
      change 0 < Nat.card (G ⧸ H) at h
      rw [Nat.card_pos_iff] at h
      exact h.2
    apply le_trans _ (Finset.card_image_le (f := QuotientGroup.mk (s := H) ∘ g))
    apply le_of_eq
    rw [Subgroup.index, ← Set.ncard_univ, ← Set.ncard_coe_Finset]
    apply congr_arg
    simp only [Finset.coe_image, Function.comp_apply]
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro x _
      induction' x using QuotientGroup.induction_on with x
      have : ∃ i ∈ s, x ∈ (g i) • (H : Set G) := by
        simpa [← Set.top_eq_univ, ← covers, Set.mem_iUnion, exists_prop] using Set.mem_univ x
      obtain ⟨i, hi, ⟨h, hmem, rfl⟩⟩ := this
      use i, hi
      simp only [Function.comp_apply, QuotientGroup.eq', smul_eq_mul, inv_mul_cancel_left]
      exact hmem
    · apply Set.ncard_mono
      simp only [Set.le_eq_subset, Set.subset_univ]

theorem Set.Finite.preimage'  {α : Type*} {β : Type*} {f : α → β} {s : Set β}
    (h : s.Finite) (hf : ∀ b ∈ s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  rw [← Set.biUnion_preimage_singleton] ; exact Set.Finite.biUnion h hf

/-
theorem Set.Finite.preimage'  {α : Type*} {β : Type*} {f : α → β} {s : Set β}
    (h : s.Finite) (hf : ∀ b ∈ s, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).Finite := by
  apply Set.Finite.induction_on
    (C := fun s ↦ ∀ (_ : s.Finite) (_ : ∀ b ∈ s, (f ⁻¹' {b}).Finite),
      (f ⁻¹' s).Finite) h
  · intro _ _
    simp only [preimage_empty, finite_empty]
  · intro a s _ hs hrec _ hf
    rw [← singleton_union, Set.preimage_union]
    apply Set.Finite.union -- finite_biUnion''
    · exact hf a (mem_insert a s)
    · exact hrec hs (fun b hb ↦ hf b (mem_insert_of_mem a hb))
  exact h
  exact hf
-/

theorem BHNeumann :
    (1 : ℚ) ≤ s.sum (fun i ↦ (1 : ℚ) / (H i).index) := by
  classical
  have covers' := of_finite_index_covers G s H g
  rw [← Finset.sum_filter_add_sum_filter_not s (p := fun i ↦ (H i).index ≠ 0)]
  set s' := s.filter (fun i ↦ (H i).index ≠ 0)
  apply le_add_of_le_of_nonneg ?_ (Finset.sum_nonneg (fun i _ ↦ by simp))
  let K := ⨅ (i : s'), (H i)
  have hK : K.index ≠ 0 := by
    apply Subgroup.index_iInf_ne_zero
    rintro ⟨i, hi⟩
    simp only [ne_eq, Finset.mem_filter, s'] at hi
    exact hi.2
  have hK_le : ∀ (i : s'), K ≤ H i := iInf_le _
  let S := fun (i : s') ↦ (Subgroup.exists_left_transversal (K.subgroupOf (H i)) 1).choose
  have hS : ∀ i, S i ∈ Subgroup.leftTransversals (K.subgroupOf (H i)) :=
    fun i ↦ (Subgroup.exists_left_transversal (K.subgroupOf (H i)) 1).choose_spec.1
  have hSf : ∀ i, (S i).Finite := fun i ↦ by
    apply Nat.finite_of_card_ne_zero
    rw [Subgroup.card_left_transversal (hS i),
      Subgroup.subgroupOf, Subgroup.index_comap, Subgroup.subtype_range]
    intro h
    apply hK
    rw [← Subgroup.relindex_mul_index (hK_le _), h, zero_mul]
  let κ := Σ (i : s'), (hSf i).toFinset
  let f : κ → G := fun ⟨i, x⟩ ↦ g i * x
  have covers' : ⋃ i ∈ Finset.univ, (f i) • (K : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro x
    simp only [← covers', Set.mem_iUnion, exists_prop, Finset.mem_univ, Function.comp_apply,
      Set.iUnion_true, forall_exists_index, and_imp]
    intro i hi hx
    rw [mem_leftCoset_iff] at hx
    let hSi := hS (⟨i, hi⟩ : s')
    let z := Subgroup.MemLeftTransversals.toFun hSi ⟨_, hx⟩
    use ⟨⟨i, hi⟩, ⟨z, by simp only [Set.Finite.mem_toFinset, Subtype.coe_prop]⟩⟩
    simp only [f, z]
    rw [mul_smul, mem_leftCoset_iff, Set.mem_smul_set_iff_inv_smul_mem]
    exact Subgroup.MemLeftTransversals.inv_toFun_mul_mem hSi ⟨_, hx⟩

  have := BHNeumann_of_subgroup G Finset.univ K f covers'
  simp only [Finset.card_univ, Set.Finite.mem_toFinset, Fintype.card_sigma, Finset.univ_eq_attach,
    Fintype.card_coe, κ] at this
  rw [← Nat.cast_le (α := ℚ), Nat.cast_sum] at this
  rw [← Finset.sum_attach]
  apply le_of_mul_le_mul_left (a := (K.index : ℚ))
  rw [mul_one, Finset.mul_sum]
  apply le_trans this
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_div, ← div_eq_mul_inv]
  rw [eq_div_iff ?_]
  haveI : Finite (S i) := hSf i
  simp only [← Nat.cast_mul, Nat.cast_inj]
  rw [← Set.ncard_eq_toFinset_card (S i), ← Subgroup.relindex_mul_index (hK_le i)]
  apply congr_arg₂ _ _ rfl
  rw [← Set.Nat.card_coe_set_eq, Subgroup.card_left_transversal (hS i)]
  rw [← Subgroup.comap_subtype, Subgroup.index_comap, Subgroup.subtype_range]
  · rw [← Nat.cast_zero, Function.Injective.ne_iff Nat.cast_injective]
    have hi' : ↑i ∈ s' := by exact Finset.coe_mem i
    simp only [Finset.mem_filter, s'] at hi'
    exact hi'.2
  · rw [← Nat.cast_zero, Nat.cast_lt]
    exact Nat.zero_lt_of_ne_zero hK

theorem BHNeumann' :
    ∃ i ∈ s, (H i).index ≤ s.card :=
  sorry
