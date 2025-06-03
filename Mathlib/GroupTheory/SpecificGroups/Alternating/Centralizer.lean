/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Centralizer of an element in the alternating group

Given a finite type `α`, our goal is to compute the cardinality of conjugacy classes
in `alternatingGroup α`.

* `AlternatingGroup.card_of_cycleType_mul_eq m` and `AlternatingGroup.card_of_cycleType m`
  compute the number of even permutations of given cycle type.

* `Equiv.Perm.OnCycleFactors.odd_of_centralizer_le_alternatingGroup` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then all members of the `g.cycleType` are odd.

* `Equiv.Perm.card_le_of_centralizer_le_alternating` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then the cardinality of α
  is at most `g.cycleType.sum` plus one.

* `Equiv.Perm.count_le_one_of_centralizer_le_alternating` :
  if `Subgroup.centralizer {g} ≤ alternatingGroup α`, then `g.cycleType` has no repetitions.

* `Equiv.Perm.centralizer_le_alternating_iff` :
  the previous three conditions are necessary and sufficient
  for having `Subgroup.centralizer {g} ≤ alternatingGroup α`.

TODO :
Deduce the formula for the cardinality of the centralizers
and conjugacy classes in `alternatingGroup α`.
-/

open Equiv Finset Function MulAction

variable {α : Type*} [Fintype α] [DecidableEq α] {g : Perm α}

namespace Equiv.Perm.OnCycleFactors

theorem odd_of_centralizer_le_alternatingGroup (h : Subgroup.centralizer {g} ≤ alternatingGroup α)
    (i : ℕ) (hi : i ∈ g.cycleType) :
    Odd i := by
  rw [cycleType_def g, Multiset.mem_map] at hi
  obtain ⟨c, hc, rfl⟩ := hi
  rw [← Finset.mem_def] at hc
  suffices sign c = 1 by
    rw [IsCycle.sign _, neg_eq_iff_eq_neg, ← Int.units_ne_iff_eq_neg] at this
    · rw [← Nat.not_even_iff_odd, comp_apply]
      exact fun h ↦ this h.neg_one_pow
    · rw [mem_cycleFactorsFinset_iff] at hc
      exact hc.left
  apply h
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Equiv.Perm.self_mem_cycle_factors_commute hc

end Equiv.Perm.OnCycleFactors

namespace AlternatingGroup

open Nat Equiv.Perm.OnCycleFactors Equiv.Perm

theorem map_subtype_of_cycleType (m : Multiset ℕ) :
    ({g | (g : Perm α).cycleType = m} : Finset (alternatingGroup α)).map (Embedding.subtype _) =
      if Even (m.sum + m.card) then ({g | g.cycleType = m} : Finset (Perm α)) else ∅ := by
  split_ifs with hm
  · ext g
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Embedding.coe_subtype, Subtype.exists, mem_alternatingGroup, exists_and_left,
      exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
    intro hg
    rw [sign_of_cycleType, hg, Even.neg_one_pow hm]
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro g hg
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Embedding.coe_subtype, Subtype.exists, mem_alternatingGroup, exists_and_left,
      exists_prop, exists_eq_right_right] at hg
    rcases hg with ⟨hg, hs⟩
    rw [g.sign_of_cycleType, hg, neg_one_pow_eq_one_iff_even (by simp)] at hs
    contradiction

variable (α) in
/-- The cardinality of even permutations of given `cycleType` -/
theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    #{g : alternatingGroup α |  g.val.cycleType = m} *
        ((Fintype.card α - m.sum)! * m.prod * (∏ n ∈ m.toFinset, (m.count n)!)) =
          if ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m))
          then (Fintype.card α)!
          else 0 := by
  rw [← Finset.card_map, map_subtype_of_cycleType, apply_ite Finset.card,
    Finset.card_empty, ite_mul, zero_mul]
  simp only [and_comm (b := Even _)]
  rw [ite_and, Equiv.Perm.card_of_cycleType_mul_eq]

variable (α) in
/-- The cardinality of even permutations of given `cycleType` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    #{g : alternatingGroup α | (g : Equiv.Perm α).cycleType = m} =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) ∧ Even (m.sum + Multiset.card m) then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! *
            (m.prod * (∏ n ∈ m.toFinset, (m.count n)!)))
      else 0 := by
  split_ifs with hm
  · -- m is an even cycle_type
    rw [← Finset.card_map, map_subtype_of_cycleType, if_pos hm.2,
      Equiv.Perm.card_of_cycleType α m, if_pos hm.1, mul_assoc]
  · -- m does not correspond to a permutation, or to an odd one,
    rw [← Finset.card_map, map_subtype_of_cycleType]
    rw [apply_ite Finset.card, Finset.card_empty]
    split_ifs with hm'
    · rw [Equiv.Perm.card_of_cycleType, if_neg]
      obtain hm | hm := not_and_or.mp hm
      · exact hm
      · contradiction
    · rfl

open Fintype in
/-- The number of cycles of given length -/
lemma card_of_cycleType_singleton {n : ℕ} (hn : 2 ≤ n) (hα : n ≤ card α) :
    #{g : alternatingGroup α | g.val.cycleType = {n}} =
      if Odd n then (n - 1)! * (choose (card α) n) else 0 := by
  rw [← card_map, map_subtype_of_cycleType, apply_ite Finset.card]
  simp only [Multiset.sum_singleton, Multiset.card_singleton, Finset.card_empty]
  simp_rw [← Nat.not_odd_iff_even, Nat.odd_add_one, not_not,
    Perm.card_of_cycleType_singleton hn hα]

end AlternatingGroup

namespace Equiv.Perm

open Basis OnCycleFactors

theorem card_le_of_centralizer_le_alternating (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    Fintype.card α ≤ g.cycleType.sum + 1 := by
  by_contra! hm
  replace hm : 2 + g.cycleType.sum ≤ Fintype.card α := by omega
  suffices 1 < Fintype.card (Function.fixedPoints g) by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    suffices sign (kerParam g ⟨swap a b, 1⟩) ≠ 1 from
      this (h (kerParam_range_le_centralizer (Set.mem_range_self _)))
    simp [sign_kerParam_apply_apply, hab]
  rwa [card_fixedPoints g, Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le]
  rw [sum_cycleType]
  exact Finset.card_le_univ _

theorem count_le_one_of_centralizer_le_alternating
    (h : Subgroup.centralizer {g} ≤ alternatingGroup α) :
    ∀ i, g.cycleType.count i ≤ 1 := by
  rw [← Multiset.nodup_iff_count_le_one, Equiv.Perm.cycleType_def]
  rw [Multiset.nodup_map_iff_inj_on g.cycleFactorsFinset.nodup]
  simp only [Function.comp_apply, ← Finset.mem_def]
  by_contra! hm
  obtain ⟨c, hc, d, hd, hm, hm'⟩ := hm
  let τ : Equiv.Perm g.cycleFactorsFinset := Equiv.swap ⟨c, hc⟩ ⟨d, hd⟩
  obtain ⟨a⟩ := Equiv.Perm.Basis.nonempty g
  have hτ : τ ∈ range_toPermHom' g := fun x ↦ by
    by_cases hx : x = ⟨c, hc⟩
    · rw [hx, Equiv.swap_apply_left]; exact hm.symm
    by_cases hx' : x = ⟨d, hd⟩
    · rw [hx', Equiv.swap_apply_right]; exact hm
    · rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  set k := toCentralizer a ⟨τ, hτ⟩ with hk
  suffices hsign_k : k.val.sign = -1 by
    apply units_ne_neg_self (1 : ℤˣ)
    rw [← hsign_k, h (toCentralizer a ⟨τ, hτ⟩).prop]
  /- to prove that `hsign_k : sign k = -1` below,
  we could prove that it is the product of the transpositions with disjoint supports
  [(g ^ n) (a c), (g ^ n) (a d)], for 0 ≤ n < c.support.card,
  which are in odd number by `odd_of_centralizer_le_alternatingGroup`,
  but it will be sufficient to observe that `k ^ 2 = 1`
  (which implies that `k.cycleType` is of the form (2,2,…))
  and to control its support. -/
  have hk_cT : k.val.cycleType = Multiset.replicate k.val.cycleType.card 2 := by
    rw [Multiset.eq_replicate_card, ← pow_prime_eq_one_iff, ← Subgroup.coe_pow,
      ← Subgroup.coe_one, Subtype.coe_inj, hk, ← map_pow]
    convert MonoidHom.map_one _
    rw [← Subtype.coe_inj]
    apply Equiv.swap_mul_self
  rw [sign_of_cycleType, hk_cT]
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.card_replicate, pow_add,
    even_two, Even.mul_left, Even.neg_pow, one_pow, one_mul]
  apply Odd.neg_one_pow
  apply odd_of_centralizer_le_alternatingGroup h
  have this : (k : Perm α).cycleType.card * 2 = (k : Perm α).support.card := by
    rw [← sum_cycleType, hk_cT]
    simp
  have that : Multiset.card (k : Perm α).cycleType = (c : Perm α).support.card := by
    rw [← Nat.mul_left_inj (a := 2) (by norm_num), this]
    simp only [hk, toCentralizer, MonoidHom.coe_mk, OneHom.coe_mk, card_ofPermHom_support]
    have H : (⟨c, hc⟩ : g.cycleFactorsFinset) ≠ ⟨d, hd⟩ := Subtype.coe_ne_coe.mp hm'
    simp only [τ, support_swap H]
    rw [Finset.sum_insert (by simp only [mem_singleton, H, not_false_eq_true]),
      Finset.sum_singleton, hm, mul_two]
  rw [that]
  simp only [cycleType_def, Multiset.mem_map]
  exact ⟨c, hc, by simp only [Function.comp_apply]⟩

theorem OnCycleFactors.kerParam_range_eq_centralizer_of_count_le_one
    (h_count : ∀ i, g.cycleType.count i ≤ 1) :
    (kerParam g).range = Subgroup.centralizer {g} := by
  ext x
  refine ⟨fun hx ↦ kerParam_range_le_centralizer hx, fun hx ↦ ?_⟩
  simp_rw [kerParam_range_eq, Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype,
    Subtype.exists, exists_and_right, exists_eq_right]
  use hx
  ext c : 2
  rw [← Multiset.nodup_iff_count_le_one, cycleType_def,
    Multiset.nodup_map_iff_inj_on (cycleFactorsFinset g).nodup] at h_count
  exact h_count _ (by simp) _ c.prop ((mem_range_toPermHom_iff).mp (by simp) c)

/-- The centralizer of a permutation is contained in the alternating group if and only if
its cycles have odd length, with at most one of each, and there is at most one fixed point. -/
theorem centralizer_le_alternating_iff :
    Subgroup.centralizer {g} ≤ alternatingGroup α ↔
      (∀ c ∈ g.cycleType, Odd c) ∧ Fintype.card α ≤ g.cycleType.sum + 1 ∧
        ∀ i, g.cycleType.count i ≤ 1 := by
  rw [SetLike.le_def]
  constructor
  · intro h
    exact ⟨odd_of_centralizer_le_alternatingGroup h,
      card_le_of_centralizer_le_alternating h,
      count_le_one_of_centralizer_le_alternating h⟩
  · rintro ⟨h_odd, h_fixed, h_count⟩ x hx
    rw [← kerParam_range_eq_centralizer_of_count_le_one h_count] at hx
    obtain ⟨⟨y, uv⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [mem_alternatingGroup, sign_kerParam_apply_apply (g := g) y uv]
    convert mul_one _
    · apply Finset.prod_eq_one
      rintro ⟨c, hc⟩ _
      obtain ⟨k, hk⟩ := (uv _).prop
      rw [← hk, map_zpow]
      convert one_zpow k
      rw [IsCycle.sign, Odd.neg_one_pow, neg_neg]
      · apply h_odd
        rw [cycleType_def, Multiset.mem_map]
        exact ⟨c, hc, rfl⟩
      · rw [mem_cycleFactorsFinset_iff] at hc
        exact hc.left
    · suffices y = 1 by simp [this]
      have := card_fixedPoints g
      exact card_support_le_one.mp <| le_trans (Finset.card_le_univ _) (by omega)

namespace IsThreeCycle

variable (h5 : 5 ≤ Fintype.card α) {g : alternatingGroup α} (hg : IsThreeCycle (g : Perm α))

include h5 hg

theorem mem_commutatorSet_alternatingGroup : g ∈ commutatorSet (alternatingGroup α) := by
  apply mem_commutatorSet_of_isConj_sq
  apply alternatingGroup.isThreeCycle_isConj h5 hg
  simpa [sq] using hg.isThreeCycle_sq

theorem mem_commutator_alternatingGroup : g ∈ commutator (alternatingGroup α) := by
  rw [commutator_eq_closure]
  apply Subgroup.subset_closure
  exact hg.mem_commutatorSet_alternatingGroup h5

end IsThreeCycle

end Equiv.Perm

section Perfect

open Subgroup Equiv.Perm

theorem alternatingGroup.commutator_perm_le :
    commutator (Perm α) ≤ alternatingGroup α := by
  simp only [commutator_eq_closure, closure_le, Set.subset_def, mem_commutatorSet_iff,
    SetLike.mem_coe, mem_alternatingGroup, forall_exists_index]
  rintro _ p q rfl
  simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, Commute.all]

/-- If `n ≥ 5`, then the alternating group on `n` letters is perfect -/
theorem commutator_alternatingGroup_eq_top (h5 : 5 ≤ Fintype.card α) :
    commutator (alternatingGroup α) = ⊤ := by
  suffices closure {b : alternatingGroup α | (b : Perm α).IsThreeCycle} = ⊤ by
    rw [eq_top_iff, ← this, Subgroup.closure_le]
    intro b hb
    exact hb.mem_commutator_alternatingGroup h5
  rw [← closure_three_cycles_eq_alternating]
  exact Subgroup.closure_closure_coe_preimage

/-- If `n ≥ 5`, then the alternating group on `n` letters is perfect (subgroup version) -/
theorem commutator_alternatingGroup_eq_self (h5 : 5 ≤ Fintype.card α) :
    ⁅alternatingGroup α, alternatingGroup α⁆ = alternatingGroup α := by
  rw [← Subgroup.map_subtype_commutator, commutator_alternatingGroup_eq_top h5,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The commutator subgroup of the permutation group is the alternating group -/
theorem alternatingGroup.commutator_perm_eq (h5 : 5 ≤ Fintype.card α) :
    commutator (Perm α) = alternatingGroup α := by
  apply le_antisymm alternatingGroup.commutator_perm_le
  rw [← commutator_alternatingGroup_eq_self h5]
  exact commutator_mono le_top le_top

end Perfect
