/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Centralizer of an element in the alternating group

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `alternatingGroup α`.

* `AlternatingGroup.of_cycleType_eq m` and `AlternatingGroup.card_of_cycleType m`
compute the number of even permutations of given cycle type.

* `Equiv.Perm.OnCycleFactors.sign_kerParam` computes the signature
of the permutation induced given by `Equiv.Perm.Basis.kerParam`.

* `Equiv.Perm.odd_of_centralizer_le_alternatingGroup`,
`card_le_of_centralizer_le_alternating`

* Finally, `Equiv.Perm.OnCycleFactors.kerφ_le_alternating_iff`
  establishes on which iff-condition the centralizer of an even permutation
  is contained in `alternatingGroup α`.

TODO :
Deduce the formula for the cardinality of the centralizers
and conjugacy classes in `alternatingGroup α`.
-/

open Equiv Finset Function MulAction

variable {α : Type*} [Fintype α] [DecidableEq α] (g : Perm α)

namespace Equiv.Perm.OnCycleFactors

theorem sign_kerParam_apply_apply
    (k : Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) :
    sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign (v c : Perm α) := by
  rw [kerParam, MonoidHom.noncommCoprod_apply, ← Prod.fst_mul_snd ⟨k, v⟩, Prod.mk_mul_mk, mul_one,
    one_mul, map_mul, sign_ofSubtype, Finset.univ_eq_attach, mul_right_inj, ← MonoidHom.comp_apply,
    Subgroup.noncommPiCoprod, MonoidHom.comp_noncommPiCoprod _, MonoidHom.noncommPiCoprod_apply,
    univ_eq_attach, noncommProd_eq_prod]
  simp

theorem cycleType_kerParam_apply_apply
    (k : Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) :
    cycleType (kerParam g ⟨k, v⟩) = cycleType k + ∑ c, cycleType (v c : Perm α) := by
  let U := (Finset.univ : Finset { x // x ∈ g.cycleFactorsFinset }).toSet
  have hU : U.Pairwise fun i j ↦ (v i : Perm α).Disjoint (v j : Perm α) := fun c _ d _ h ↦ by
    obtain ⟨m, hm⟩ := (v c).prop
    obtain ⟨n, hn⟩ := (v d).prop
    simp only [← hm, ← hn]
    apply Disjoint.zpow_disjoint_zpow
    apply cycleFactorsFinset_pairwise_disjoint g c.prop d.prop
    exact Subtype.coe_ne_coe.mpr h
  rw [kerParam, MonoidHom.noncommCoprod_apply, ← Prod.fst_mul_snd ⟨k, v⟩, Prod.mk_mul_mk, mul_one,
    one_mul, univ_eq_attach, Disjoint.cycleType (disjoint_ofSubtype_noncommPiCoprod g k v),
    Subgroup.noncommPiCoprod_apply, Disjoint.cycleType_noncommProd hU, univ_eq_attach]
  exact congr_arg₂ _ cycleType_ofSubtype rfl

variable {g} in
theorem odd_of_centralizer_le_alternatingGroup
    (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    ∀ i ∈ g.cycleType, Odd i := by
  intro i hi
  rw [cycleType_def g, Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices sign c = 1 by
    rw [IsCycle.sign _, neg_eq_iff_eq_neg] at this
    · rw [← Nat.not_even_iff_odd, Function.comp_apply]
      rw [← Int.units_ne_iff_eq_neg] at this
      exact fun h ↦ this h.neg_one_pow
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  apply h
  apply kerParam_range_le_centralizer
  -- apply Subgroup.map_subtype_le (toPermHom g).ker
  -- rw [← kerParam_range_eq, kerParam]
  rw [kerParam]
  use ⟨1, Pi.mulSingle ⟨c, hc⟩ ⟨c, Subgroup.mem_zpowers c⟩⟩
  simp

end Equiv.Perm.OnCycleFactors

namespace AlternatingGroup

open Nat Equiv.Perm.OnCycleFactors Equiv.Perm

private theorem of_cycleType_aux (m : Multiset ℕ) :
    map (Function.Embedding.subtype fun x ↦ x ∈ alternatingGroup α)
      (univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m) =
      if Even (m.sum + Multiset.card m)
        then Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m
        else ∅ := by
  split_ifs with hm
  · ext g
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, Subtype.exists, mem_alternatingGroup, exists_and_left,
      exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
    intro hg
    rw [sign_of_cycleType, hg, Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_not_mem]
    intro g hg
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype, Subtype.exists, mem_alternatingGroup, exists_and_left,
      exists_prop, exists_eq_right_right] at hg
    rcases hg with ⟨hg, hs⟩
    apply hm
    rwa [g.sign_of_cycleType, hg, neg_one_pow_eq_one_iff_even] at hs
    exact neg_units_ne_self 1

/-- The cardinality of even permutations of given `cycleType` -/
theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card *
        ((Fintype.card α - m.sum)! *
          (m.prod * (∏ n ∈ m.toFinset, (m.count n)!))) =
      if ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m))
        then (Fintype.card α)!
        else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map, AlternatingGroup.of_cycleType_aux, if_pos hm.2]
    simp only [← mul_assoc, Equiv.Perm.card_of_cycleType_mul_eq α m, if_pos hm.1]
  · -- m does not correspond to a permutation, or corresponds to an odd one,
    rw [← Finset.card_map, AlternatingGroup.of_cycleType_aux,
      apply_ite Finset.card, Finset.card_empty]
    rw [not_and_or] at hm
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg, zero_mul]
      cases' hm with hm hm
      · exact hm
      · exfalso; exact hm hm'
    · rw [zero_mul]

/-- The cardinality of even permutations of given `cycleType` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! *
            (m.prod * (∏ n ∈ m.toFinset, (m.count n)!)))
      else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map, AlternatingGroup.of_cycleType_aux, if_pos hm.2,
    Equiv.Perm.card_of_cycleType α m]
    rw [if_pos hm.1, mul_assoc]
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map, AlternatingGroup.of_cycleType_aux]
    rw [apply_ite Finset.card, Finset.card_empty]
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg]
      cases' not_and_or.mp hm with hm hm
      · exact hm
      · contradiction
    · rfl

namespace OnCycleFactors

open Basis

theorem card_le_of_centralizer_le_alternating
    (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    Fintype.card α ≤ g.cycleType.sum + 1 := by
  rw [← not_lt]
  intro hm
  rw [Nat.lt_iff_add_one_le, add_assoc, add_comm] at hm
  change 2 + g.cycleType.sum ≤ _ at hm
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (kerParam g ⟨swap a b, 1⟩) ≠ 1 by
      exact this (h (kerParam_range_le_centralizer (Set.mem_range_self _)))
    simp [sign_kerParam, hab]
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _

theorem count_le_one_of_centralizer_le_alternating
    (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    ∀ i, g.cycleType.count i ≤ 1 := by
  rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra hm
  push_neg at hm
  obtain ⟨c, hc, d, hd, hm, hm'⟩ := hm
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := Equiv.Perm.Basis.nonempty g
  suffices hτ : τ ∈ range_toPermHom' g by
    set k := toCentralizer a ⟨τ, hτ⟩ with hk
    suffices hsign_k : Equiv.Perm.sign (k : Perm α) = -1 by
      rw [h _, ← Units.eq_iff] at hsign_k
      exact Int.noConfusion hsign_k
      exact (toCentralizer a ⟨τ, hτ⟩).prop
    /- to prove that `sign k = -1`,
      we could prove that it is the product
      of the transpositions with disjoint supports
      [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
      which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
      but it will be sufficient to observe that `k ^ 2 = 1`
      (which implies that `k.cycleType` is of the form (2,2,…))
      and to control its support. -/
    suffices ∀ b ∈ (k : Perm α).cycleType, b = 2 by
      let this' := Multiset.eq_replicate_card.mpr this
      rw [sign_of_cycleType, this']
      simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate]
      rw [Odd.neg_one_pow]
      rw [Nat.odd_add']
      simp only [even_two, Even.mul_left, iff_true]
      apply odd_of_centralizer_le_alternatingGroup h
      suffices that : Multiset.card (k : Perm α).cycleType = (c : Perm α).support.card by
        rw [that]
        simp only [cycleType_def, Multiset.mem_map]
        exact ⟨c , hc, by simp only [Function.comp_apply]⟩
      have this'' : (k : Perm α).cycleType.sum = (k : Perm α).support.card :=
        sum_cycleType _
      rw [this', Multiset.sum_replicate, smul_eq_mul] at this''
      rw [← mul_left_inj' (c := 2) (by norm_num), this'']
      simp only [hk, toCentralizer, MonoidHom.coe_mk, OneHom.coe_mk, card_ofPermHom_support]
      have H : (⟨c, hc⟩ : g.cycleFactorsFinset) ≠ ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
      simp only [τ, support_swap H]
      rw [Finset.sum_insert (by simp only [mem_singleton, H, not_false_eq_true]),
        Finset.sum_singleton]
      rw [Equiv.Perm.OnCycleFactors.mem_range_toPermHom'_iff] at hτ
      specialize hτ ⟨c, hc⟩
      simp only [τ, Equiv.swap_apply_left] at hτ
      rw [hτ, mul_two]
    rw [← pow_prime_eq_one_iff, ← Subgroup.coe_pow, ← Subgroup.coe_one, Subtype.coe_inj]
    simp only [k, ← map_pow]
    suffices  (⟨τ, hτ⟩ : range_toPermHom' g) ^ 2 = 1  by
      simp only [this, map_one, OneMemClass.coe_one]
    rw [← Subtype.coe_inj]
    simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one, τ]
    simp only [pow_two, Equiv.swap_mul_self]
  intro x
  by_cases hx : x = ⟨c, hc⟩
  · rw [hx, Equiv.swap_apply_left]; exact hm.symm
  by_cases hx' : x = ⟨d, hd⟩
  · rw [hx', Equiv.swap_apply_right]; exact hm
  · rw [Equiv.swap_apply_of_ne_of_ne hx hx']

end OnCycleFactors

end AlternatingGroup

namespace Equiv.Perm

open OnCycleFactors AlternatingGroup.OnCycleFactors

theorem kerParam_range_eq_centralizer_of_count_le_one (h_count : ∀ i, g.cycleType.count i ≤ 1) :
    (kerParam g).range = Subgroup.centralizer {g} := by
  ext x
  constructor
  · apply kerParam_range_le_centralizer
  · intro hx
    rw [kerParam_range_eq]
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coeSubtype, Subtype.exists,
      exists_and_right, exists_eq_right]
    use hx
    have that := mem_range_toPermHom_iff (τ := (toPermHom g) ⟨x, hx⟩)
    simp only [MonoidHom.mem_range, exists_apply_eq_apply, true_iff] at that
    ext1 c
    rw [← Multiset.nodup_iff_count_le_one, cycleType_def,
      Multiset.nodup_map_iff_inj_on (cycleFactorsFinset g).nodup] at h_count
    rw [coe_one, id_eq, ← Subtype.coe_inj]
    apply h_count _ _ _ c.prop (that c)
    simp only [Finset.mem_val, Finset.coe_mem]

/-- The centralizer of a permutation is contained in the alternating group if and only if
all cycles have odd length, with at most one of each, and there is at most one fixed point. -/
theorem centralizer_le_alternating_iff :
    Subgroup.centralizer {g} ≤ alternatingGroup α ↔
    (∀ c ∈ g.cycleType, Odd c) ∧ Fintype.card α ≤ g.cycleType.sum + 1 ∧
      ∀ i, g.cycleType.count i ≤ 1 :=  by
  rw [SetLike.le_def]
  constructor
  · intro h
    exact ⟨odd_of_centralizer_le_alternatingGroup h,
      card_le_of_centralizer_le_alternating g h,
      count_le_one_of_centralizer_le_alternating g h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    rw [← kerParam_range_eq_centralizer_of_count_le_one g h_count] at hx
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [mem_alternatingGroup]
    have := sign_kerParam (g := g) y uv
    rw [this]
    convert mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk, map_zpow]
      convert one_zpow k
      simp only
      rw [IsCycle.sign, Odd.neg_one_pow, neg_neg]
      · apply h_odd
        rw [cycleType_def, Multiset.mem_map]
        exact ⟨c, hc, rfl⟩
      · rw [mem_cycleFactorsFinset_iff] at hc
        exact hc.left
    · apply symm
      convert sign_one
      rw [← card_support_le_one]
      apply le_trans (Finset.card_le_univ _)
      rw [card_fixedPoints g, tsub_le_iff_left]
      exact h_fixed

end Equiv.Perm
