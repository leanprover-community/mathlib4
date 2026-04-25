/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-! # The alternating group is simple

* `Equiv.Perm.iwasawaStructure_two`:
  the natural `IwasawaStructure` of `Equiv.Perm α` acting on `Set.powersetCard α 2`.
  Its commutative subgroups consist of the permutations with support in a given element
  of `Set.powersetCard α 2`. They are cyclic of order 2.

* `alternatingGroup_of_le_of_normal`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup
  of `Equiv.Perm α` contains the alternating group.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 3`.

  Its commutative subgroups consist of the permutations with support
  in a given element of `Set.powersetCard α 2`. They are cyclic of order 3.

* `alternatingGroup.iwasawaStructure_four`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 4`

  Its commutative subgroups consist of the permutations of cycleType (2, 2) with support
  in a given element of `Set.powersetCard α 2`. They have order 4 and exponent 2 (`IsKleinFour`).

* `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup of `alternatingGroup` is `⊤`.

* `alternatingGroup.isSimpleGroup`:
  If `α` has at least 5 elements, then `alternatingGroup α` is a simple group.

-/

@[expose] public section

open scoped Pointwise

open MulAction Equiv.Perm Equiv Set.powersetCard

namespace Equiv.Perm

variable {α : Type*} [Finite α] [DecidableEq α]

/-- The Iwasawa structure of `Perm α` acting on `Set.powersetCard α 2`. -/
def iwasawaStructure_two [∀ s : Set α, DecidablePred fun x ↦ x ∈ s] :
    IwasawaStructure (Perm α) (Set.powersetCard α 2) where
  T s := (ofSubtype : Perm (s : Set α) →* Perm α).range
  is_comm s := by
    have : IsMulCommutative (Perm s) := isMulCommutative_iff_card_le_two.mpr (by simp)
    infer_instance
  is_conj g s := by
    convert (conj_smul_range_ofSubtype g s).symm
  is_generator := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    rintro g ⟨a, b, hab, rfl⟩
    apply Subgroup.mem_iSup_of_mem ⟨{a, b}, Finset.card_pair hab⟩
    exact ⟨swap ⟨a, by simp⟩ ⟨b, by simp⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

/-- If `α` has at least 5 elements, then the only nontrivial
normal subgroup of `Equiv.Perm α` is `alternatingGroup α`. -/
theorem alternatingGroup_of_le_of_normal
    {α : Type*} [DecidableEq α] [Fintype α] (hα : 5 ≤ Nat.card α)
    {N : Subgroup (Perm α)} (hnN : N.Normal) (ntN : Nontrivial N) :
    alternatingGroup α ≤ N := by
  rw [← alternatingGroup.commutator_perm_eq hα]
  have : IsPreprimitive (Perm α) (Set.powersetCard α 2) := by
    apply Set.powersetCard.isPreprimitive_perm <;> grind
  classical
  apply iwasawaStructure_two.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul 2 (by norm_num) (by grind)

end Equiv.Perm

namespace alternatingGroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 3`. -/
def iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Set.powersetCard α 3) where
  T s := (alternatingGroup.ofSubtype s).range
  is_comm s := by
    have : IsMulCommutative (alternatingGroup s) := isMulCommutative_of_card_le_three (by simp)
    infer_instance
  is_conj g s := (conj_smul_range_ofSubtype s g).symm
  is_generator := by
    rw [eq_top_iff, ← closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro g hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
    rw [mem_range_ofSubtype_iff]

/-- If `α` has at least 5 elements, but not 6,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 6)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  rw [or_iff_not_imp_left, ← ne_eq, ← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 3) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · exact lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff, ← commutator_alternatingGroup_eq_top (by simpa using hα)]
  apply iwasawaStructure_three.commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul 3 (by norm_num) (by grind)

theorem mem_map_kleinFour_ofSubtype (s : Finset α) (hs : s.card = 4) (k : alternatingGroup α) :
    k ∈ (kleinFour s).map (ofSubtype s) ↔
      (k : Perm α).support ⊆ s ∧ ((k : Perm α) = 1 ∨ (k : Perm α).cycleType = {2, 2}) := by
  have hs : Nat.card s = 4 := by simpa
  by_cases hk : (k : Perm α).support ⊆ s
  · obtain ⟨σ, rfl⟩ := (mem_range_ofSubtype_iff s k).mpr hk
    simp_rw [and_iff_right hk, Subgroup.mem_map, ofSubtype_inj, existsAndEq, and_true,
      ← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs]
    simp only [Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq, OneMemClass.coe_eq_one,
      cycleType_ofSubtype, coe_ofSubtype, map_eq_one_iff _ Perm.ofSubtype_injective]
    convert Iff.rfl
  · simp_rw [hk, false_and, iff_false]
    contrapose! hk
    exact (mem_range_ofSubtype_iff s k).mp (Subgroup.map_le_range _ _ hk)

theorem map_kleinFour_conj (s : Finset α) (hs : s.card = 4) (g : alternatingGroup α) :
    (kleinFour _).map (ofSubtype (g • s)) = MulAut.conj g • ((kleinFour s).map (ofSubtype s)) := by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map_kleinFour_ofSubtype s hs,
    Subgroup.mk_smul, MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, ← ConjAct.toConjAct_inv_smul, Equiv.Perm.support_toConjAct_eq_smul_support,
    mem_map_kleinFour_ofSubtype (g • s) (by simpa), Finset.subset_smul_finset_iff,
    ConjAct.toConjAct_smul, cycleType_conj, mul_inv_eq_one, mul_eq_left]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 4`,
provided `α` has at least 5 elements. -/
def iwasawaStructure_four (h5 : 5 ≤ Nat.card α) :
    IwasawaStructure (alternatingGroup α) (Set.powersetCard α 4) where
  T s := (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by simp)).isMulCommutative
    infer_instance
  is_conj g s := map_kleinFour_conj s.val s.prop g
  is_generator := by
    rw [eq_top_iff, ← closure_cycleType_eq_two_two_eq_top h5, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype] <;> simp [hg, ← sum_cycleType]

/-- If `α` has at least 5 elements, but not 8,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 8)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  rw [or_iff_not_imp_left, ← ne_eq, ← Subgroup.nontrivial_iff_ne_bot]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 4) := by
    apply Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) <;> grind
  rw [eq_top_iff, ← commutator_alternatingGroup_eq_top hα]
  apply (iwasawaStructure_four hα).commutator_le
  exact fixedPoints_ne_univ_of_faithfulSMul 4 (by norm_num) (by grind)

/- If `α` has at least 5 elements,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top
    (hα : 5 ≤ Nat.card α)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight hα (by grind) hnN
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_six hα hα' hnN

/-- When `α` has at least 5 elements, then `alternatingGroup α` is a simple group. -/
public theorem isSimpleGroup (hα : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α) where
  exists_pair_ne := by
    rw [← nontrivial_iff]
    refine nontrivial_of_three_le_card ?_
    simpa using le_trans (by norm_num) hα
  eq_bot_or_eq_top_of_normal H := normal_subgroup_eq_bot_or_eq_top hα

end alternatingGroup
