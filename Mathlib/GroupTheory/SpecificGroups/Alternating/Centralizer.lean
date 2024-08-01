/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! #Centralizer of an alement in the alternating group
Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `alternatingGroup α`.

* `AlternatingGroup.of_cycleType_eq m` and `AlternatingGroup.card_of_cycleType m`
  give the analogous result in the subgroup `alternatingGroup α`

* `Equiv.Perm.OnCycleFactors.sign_θ` computes the signature of the permutation induced given by `Equiv.Perm.Basis.θ`.

* Finally, `Equiv.Perm.OnCycleFactors.kerφ_le_alternating_iff`
  establishes on which iff-condition the centralizer of an even permutation
  is contained in `alternatingGroup α`.

  TODO : deduce the formula for the cardinality of the centralizers
  and conjugacy classes in `alternatingGroup α`.


-/
variable {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α)

namespace Equiv.Perm.OnCycleFactors

open Equiv.Perm Equiv Finset MulAction

theorem sign_θ
    (k : Perm (Function.fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) :
    sign (θ g ⟨k, v⟩) = sign k *
        Finset.univ.prod fun c => sign (v c : Perm α) :=  by
  rw [← Prod.fst_mul_snd ⟨k, v⟩]
  simp only [map_mul]
  apply congr_arg₂
  · simp only [θ_apply_fst, sign_ofSubtype]
  · rw [← MonoidHom.inr_apply, ← MonoidHom.comp_apply]
    conv_lhs => rw [← Finset.noncommProd_mul_single v]
    simp only [Finset.noncommProd_map]
    rw [Finset.noncommProd_eq_prod]
    apply Finset.prod_congr rfl
    intro c _
    simp only [MonoidHom.inr_apply, MonoidHom.coe_comp, Function.comp_apply]
    rw [θ_apply_single_zpowers]

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
    · rw [Nat.odd_iff_not_even, Function.comp_apply]
      rw [← neg_one_pow_eq_one_iff_even (R := ℤˣ) (by norm_num), this]
      norm_num
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  suffices c = θ g ⟨1, Pi.mulSingle ⟨c, hc⟩ ⟨c, Subgroup.mem_zpowers c⟩⟩ by
    rw [this]
    apply h
    rw [Subgroup.centralizer_eq, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    apply Subgroup.map_subtype_le
    rw [hφ_ker_eq_θ_range]
    exact Set.mem_range_self _
  rw [θ_apply_single]

end Equiv.Perm.OnCycleFactors

namespace AlternatingGroup

open BigOperators Nat Equiv.Perm.OnCycleFactors Equiv.Perm

open Equiv.Perm Finset

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

/-- The cardinality of even permutation of given `cycleType` -/
theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card *
        ((Fintype.card α - m.sum)! *
          (m.prod * (∏ n in m.toFinset, (m.count n)!))) =
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
      cases' hm with hm hm; exact hm; exfalso; exact hm hm'
    · rw [zero_mul]

/-- The cardinality of even permutation of given `cycleType` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter fun g : alternatingGroup α => (g : Equiv.Perm α).cycleType = m).card =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! *
            (m.prod * (∏ n in m.toFinset, (m.count n)!)))
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

open Basis Equiv.Perm Equiv.Perm.OnCycleFactors Equiv

theorem card_le_of_centralizer_le_alternating
    (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    Fintype.card α ≤ g.cycleType.sum + 1 := by
  rw [← not_lt]
  intro hm
  rw [Nat.lt_iff_add_one_le, add_assoc, add_comm] at hm
  change 2 + g.cycleType.sum ≤ _ at hm
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (θ g ⟨swap a b, 1⟩) ≠ 1 by
      apply this
      apply h
      rw [Subgroup.centralizer_eq, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
      apply Subgroup.map_subtype_le
      rw [hφ_ker_eq_θ_range]
      exact Set.mem_range_self _
    simp only [θ_apply_fst, ofSubtype_swap_eq, sign_swap', Subtype.coe_inj,
      ne_eq, ite_eq_left_iff, neg_units_ne_self, imp_false, Decidable.not_not]
    exact hab
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _

theorem _root_.Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
    {g : Perm α} {x y : α} (hx : x ∈ g.support) (hy : y ∈ g.support) :
    g.SameCycle x y ↔ g.cycleOf x = g.cycleOf y := by
  constructor
  · exact SameCycle.cycleOf_eq
  · intro h
    rw [← mem_support_cycleOf_iff' (mem_support.mp hx), h]
    rw [mem_support_cycleOf_iff' (mem_support.mp hy)]

-- FIND A BETTER NAME
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
  suffices hτ : τ ∈ range_toPerm' g by
    set k : Equiv.Perm α := ConjAct.ofConjAct (Equiv.Perm.Basis.ofPerm a ⟨τ, hτ⟩ : ConjAct (Equiv.Perm α))
    have hk2 : ∀ c : g.cycleFactorsFinset, ConjAct.toConjAct k • (c : Equiv.Perm α) = τ c := by
      intro c
      rw [ConjAct.smul_def]
      simp only [ConjAct.ofConjAct_toConjAct]
      rw [mul_inv_eq_iff_eq_mul]
      ext x
      exact Equiv.Perm.Basis.k_cycle_apply a hτ c x
    have hksup : k.support ≤ g.support := by
      intro x
      simp only [Equiv.Perm.mem_support, not_imp_not]
      intro hx
      rw [← Equiv.Perm.not_mem_support] at hx
      exact k_apply_of_not_mem_support a x hx
    suffices hsign_k : Equiv.Perm.sign k = -1 by
      rw [h _, ← Units.eq_iff] at hsign_k
      exact Int.noConfusion hsign_k
      rw [Subgroup.centralizer_eq]
      exact (ofPerm a ⟨τ, hτ⟩).prop
    /- to prove that `sign k = -1`,
      we could prove that it is the product
      of the transpositions with disjoint supports
      [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
      which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
      but it will be sufficient to observe that `k ^ 2 = 1`
      (which implies that `k.cycleType` is of the form (2,2,…))
      and to control its support. -/
    suffices k.cycleType = Multiset.replicate c.support.card 2 by
      rw [Equiv.Perm.sign_of_cycleType]; rw [this]
      simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate]
      rw [Odd.neg_one_pow]
      rw [Nat.odd_add']
      simp only [odd_of_centralizer_le_alternatingGroup h c.support.card
        (by rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
            exact ⟨c, hc, rfl⟩),
        true_iff_iff]
      rw [mul_comm]; apply even_two_mul
    have hk_apply (c : g.cycleFactorsFinset) (m n : ℕ) :
        (k ^ m) ((g ^ n : Equiv.Perm α) (a c)) = (g ^ n) (a ((τ ^ m) c)) := by
      suffices ∀ m n : ℕ, Commute (k ^ m) (g ^ n) by
        simp only [commute_iff_eq] at this
        rw [← Equiv.Perm.mul_apply, this, Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq]
        simp only [k, map_pow, ← k_apply_base]
        rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, ofPerm_apply_mk', SubmonoidClass.mk_pow]
        rw [k_apply_base]
        have : τ ^ m ∈ range_toPerm' g := Subgroup.pow_mem _ hτ m
        rw [mem_range_toPerm'_iff] at this
        exact this
      apply Commute.pow_pow
      rw [commute_iff_eq, ← mul_inv_eq_iff_eq_mul]
      exact (ofPerm a ⟨τ, hτ⟩).prop

    suffices ∀ i ∈ k.cycleType, i = 2 by
      rw [← Multiset.eq_replicate_card] at this
      rw [this]
      congr
      --
      have this' : Multiset.sum (Equiv.Perm.cycleType k) = Finset.card (Equiv.Perm.support k) := k.sum_cycleType
      rw [this] at this'
      simp only [Multiset.sum_replicate, smul_eq_mul] at this'
      rw [← mul_left_inj']
      rw [this']
      rw [Equiv.Perm.Basis.card_ofPerm_support a ⟨τ, hτ⟩ rfl]
      simp only [τ]
      have H : (⟨c, hc⟩ : g.cycleFactorsFinset) ≠ ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
      rw [Equiv.Perm.support_swap H]
      rw [Finset.sum_insert, Finset.sum_singleton]
      · simp only
        rw [Equiv.Perm.OnCycleFactors.mem_range_toPerm'_iff] at hτ
        specialize hτ ⟨c, hc⟩
        simp only [τ, Equiv.swap_apply_left] at hτ
        rw [hτ, mul_two]
      · simp only [Finset.mem_singleton, H, not_false_eq_true]
      · norm_num

   -- ∀ i ∈ k.cycle_type, i = 2
    suffices hk2 : orderOf k = 2 by
      have hk2' : Nat.Prime (orderOf k) := by
        rw [hk2]; exact Nat.prime_two
      obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hk2'
      intro i hi
      rw [hn, hk2, Multiset.mem_replicate] at hi
      exact hi.right
    apply orderOf_eq_prime
    · -- k ^ 2 = 1,
      simp only [k, ← map_pow]
      rw [← Subgroup.coe_pow, ← map_pow]
      suffices  (⟨τ, hτ⟩ : range_toPerm' g) ^ 2 = 1  by
        simp only [this, map_one, OneMemClass.coe_one]
      rw [← Subtype.coe_inj]
      simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one, τ]
      simp only [pow_two, Equiv.swap_mul_self]
    · -- k ≠ 1
      intro hk
      specialize hk2 ⟨c, hc⟩
      simp only [hk, ConjAct.toConjAct_one, Subtype.coe_mk, one_smul,
        Equiv.swap_apply_left, τ] at hk2
      exact hm' hk2
  · intro x
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']

end OnCycleFactors

end AlternatingGroup

namespace Equiv.Perm

open OnCycleFactors AlternatingGroup.OnCycleFactors

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
    suffices hx' : x ∈ (θ g).range by
      obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx'
      rw [Equiv.Perm.mem_alternatingGroup]
      have := sign_θ (g := g) y uv
      rw [this]
      convert mul_one _
      · apply Finset.prod_eq_one
        rintro ⟨c, hc⟩ _
        obtain ⟨k, hk⟩ := (uv _).prop
        rw [← hk, map_zpow]
        convert one_zpow k
        simp only
        rw [Equiv.Perm.IsCycle.sign, Odd.neg_one_pow, neg_neg]
        · apply h_odd
          rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
          exact ⟨c, hc, rfl⟩
        · rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
          exact hc.left
      · apply symm
        convert Equiv.Perm.sign_one
        rw [← Equiv.Perm.card_support_le_one]
        apply le_trans (Finset.card_le_univ _)
        rw [card_fixedPoints g, tsub_le_iff_left]
        exact h_fixed
    -- x ∈ set.range (on_cycle_factors.ψ g)
    suffices (toPerm g).ker = ⊤ by
      rw [← hφ_ker_eq_θ_range, this]
      simp only [Subgroup.coeSubtype, Subgroup.mem_map, Subgroup.mem_top, true_and]
      rw [Subgroup.centralizer_eq] at hx
      exact ⟨⟨x, hx⟩, rfl⟩
    -- (OnCycleFactors.φ g).ker = ⊤
    rw [eq_top_iff]
    intro y _
    suffices (toPerm g).range = ⊥ by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← this, MonoidHom.mem_range]
      exact ⟨y, rfl⟩
    rw [eq_bot_iff]
    intro z
    rw [mem_range_toPerm_iff, Subgroup.mem_bot]
    intro hz
    apply Equiv.ext
    intro c
    rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def,
      Multiset.nodup_map_iff_inj_on (Equiv.Perm.cycleFactorsFinset g).nodup]
      at h_count
    rw [Equiv.Perm.coe_one, id_eq, ← Subtype.coe_inj]
    apply h_count (z c) (z c).prop c c.prop (hz c)

end Equiv.Perm
