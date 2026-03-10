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
  the natural `IwasawaStructure` of `Equiv.Perm α` acting on `Set.powersetCard α 2`
  Its commutative subgroups consist of the permutations with support
  in a given element of `Set.powersetCard α 2`.
  They are cyclic of order 2.

* `alternatingGroup_of_le_of_normal`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup
  of `Equiv.Perm α` contains the alternating group.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 3`

  Its commutative subgroups consist of the permutations with support
  in a given element of `Set.powersetCard α 2`.
  They are cyclic of order 3.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Set.powersetCard α 4`

  Its commutative subgroups consist of the permutations of
  cycleType (2, 2) with support in a given element of `Set.powersetCard α 2`.
  They have order 4 and exponent 2 (`IsKleinFour`).

* `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup of `alternatingGroup` is `⊤`.

* `alternatingGroup.isSimpleGroup`:
  If `α` has at least 5 elements, then `alternatingGroup α`
  is a simple group.

-/

@[expose] public section

open scoped Pointwise

open MulAction Equiv.Perm Equiv

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α] [Finite α]

/-- The Iwasawa structure of `Perm α` acting on `Set.powersetCard α 2`. -/
def iwasawaStructure_two [∀ s : Set α, DecidablePred fun x ↦ x ∈ s] :
    IwasawaStructure (Perm α) (Set.powersetCard α 2) where
  T s := (ofSubtype : Perm (s : Set α) →* Perm α).range
  is_comm s := by
    suffices IsCyclic (Perm s) by
      let _ : CommGroup (Perm s) := IsCyclic.commGroup
      apply MonoidHom.range_isMulCommutative
    apply isCyclic_of_prime_card (p := 2)
    rw [Nat.card_perm, Nat.card_eq_finsetCard, s.prop, Nat.factorial_two]
  is_conj g s := by
    convert (conj_smul_range_ofSubtype g s).symm
  is_generator := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    intro g hg
    obtain ⟨a, b, hab, rfl⟩ := hg
    let s : Set.powersetCard α 2 := ⟨{a, b}, Finset.card_pair hab⟩
    apply Subgroup.mem_iSup_of_mem s
    exact ⟨swap ⟨a, by aesop⟩ ⟨b, by aesop⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

/-- If `α` has at least 5 elements, then the only nontrivial
normal subgroup of `Equiv.Perm α` is `alternatingGroup α`. -/
theorem alternatingGroup_of_le_of_normal
    {α : Type*} [DecidableEq α] [Fintype α] (hα : 5 ≤ Nat.card α)
    {N : Subgroup (Perm α)} (hnN : N.Normal) (ntN : Nontrivial N) :
    alternatingGroup α ≤ N := by
  rw [Nat.card_eq_fintype_card] at hα
  rw [← alternatingGroup.commutator_perm_eq hα]
  rw [← Nat.card_eq_fintype_card] at hα
  have : IsPreprimitive (Perm α) (Set.powersetCard α 2) := by
    apply Set.powersetCard.isPreprimitive_perm (by norm_num) (lt_of_lt_of_le (by norm_num) hα)
    aesop
  classical
  apply iwasawaStructure_two.commutator_le
  intro h
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN
  suffices ∃ s : Set.powersetCard α 2, g • s ≠ s by
    obtain ⟨s, hs⟩ := this
    have := Set.mem_univ s
    rw [← h, mem_fixedPoints] at this
    apply hs
    rw [← Subgroup.mk_smul g hgN, this]
  contrapose! hg_ne
  replace hg_ne : (toPerm g : Perm (Set.powersetCard α 2)) = 1 := by
    ext1 s
    exact hg_ne s
  convert hg_ne
  symm
  apply Set.powersetCard.mulAction_faithful
  · norm_num
  · have : CharZero ℕ∞ := instCharZeroENat
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_ofNat,
          Nat.ofNat_lt_cast, ← Nat.card_eq_fintype_card]
    exact le_trans (by norm_num) hα

end Equiv.Perm

namespace alternatingGroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 3`. -/
def iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Set.powersetCard α 3) where
  T s := (alternatingGroup.ofSubtype s).range
  is_comm s := by
    suffices IsCyclic (alternatingGroup s) by
      let _ : CommGroup (alternatingGroup s) := IsCyclic.commGroup
      exact MonoidHom.range_isMulCommutative (ofSubtype (s : Finset α))
    apply isCyclic_of_prime_card (p := 3)
    have : Nontrivial s := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, s.prop]
      norm_num
    rw [nat_card_alternatingGroup, Nat.card_eq_finsetCard, s.prop]
    norm_num [Nat.factorial]
  is_conj g s := range_ofSubtype_conj s g
  is_generator := by
    rw [eq_top_iff, ← closure_isThreeCycles_eq_top, Subgroup.closure_le]
    intro g hg
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
    rw [mem_range_ofSubtype]

/-- If `α` has at least 5 elements, but not 6,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_six
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 6)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 3) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · exact lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff, ← commutator_alternatingGroup_eq_top (by simpa using hα)]
  apply iwasawaStructure_three.commutator_le
  intro h
  simp_rw [Set.eq_univ_iff_forall, mem_fixedPoints] at h
  rw [← ne_eq, ← Subgroup.nontrivial_iff_ne_bot, Subgroup.nontrivial_iff_exists_ne_one] at hN
  obtain ⟨g, hgN, hg_ne⟩ := hN
  suffices ∃ s : Set.powersetCard α 3, g • s ≠ s by
    obtain ⟨s, hs⟩ := this
    apply hs
    rw [← Subgroup.mk_smul g hgN, h]
  contrapose! hg_ne
  rw [← Subtype.coe_inj]
  replace hg_ne : (toPerm g : Perm (Set.powersetCard α 3)) = 1 := by
    ext1 s
    exact hg_ne s
  convert hg_ne
  symm
  apply Set.powersetCard.mulAction_faithful
  · norm_num
  · have : CharZero ℕ∞ := instCharZeroENat
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_ofNat,
          Nat.ofNat_lt_cast, ← Nat.card_eq_fintype_card]
    apply le_trans (by norm_num) hα

theorem mem_map_kleinFour_ofSubtype (s : Finset α) (hs : s.card = 4) (k : alternatingGroup α) :
    k ∈ (kleinFour s).map (ofSubtype s) ↔
      (k : Perm α).support ⊆ s ∧
        ((k : Perm α) = 1 ∨ (k : Perm α).cycleType = {2, 2}) := by
  have hs : Nat.card s = 4 := by aesop
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [coe_kleinFour_of_card_eq_four hs,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hk
    simp only [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk, cycleType_ofSubtype,
      map_eq_one_iff _ ofSubtype_injective, OneMemClass.coe_eq_one]
    refine ⟨?_, by convert hk⟩
    intro x
    rw [mem_support_ofSubtype]
    exact Exists.choose
  · rintro ⟨hk, hk'⟩
    rw [← mem_range_ofSubtype] at hk
    obtain ⟨k, rfl⟩ := hk
    apply Subgroup.mem_map_of_mem
    rw [← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
    simp only [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk, cycleType_ofSubtype,
      map_eq_one_iff _ ofSubtype_injective, OneMemClass.coe_eq_one] at hk'
    convert hk'

theorem map_kleinFour_conj (s : Finset α) (hs : s.card = 4) (g : alternatingGroup α) :
    (kleinFour _).map (ofSubtype (g • s)) =
        MulAut.conj g • ((kleinFour s).map (ofSubtype s)) := by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_map_kleinFour_ofSubtype s hs, Subgroup.mk_smul,
    MulAut.smul_def, MulAut.inv_apply,
    MulAut.conj_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [Equiv.Perm.support_conj_eq_smul_support',
    mem_map_kleinFour_ofSubtype (g • s) (by rw [Finset.card_smul_finset, hs]),
    ← Finset.subset_smul_finset_iff]
  refine and_congr Iff.rfl (or_congr ?_ ?_)
  · simp [mul_eq_one_iff_inv_eq']
  · nth_rewrite 2 [← inv_inv g]
    rw [cycleType_conj]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Set.powersetCard α 4`,
provided `α` has at least 5 elements. -/
def iwasawaStructure_four (h5 : 5 ≤ Nat.card α) :
    IwasawaStructure (alternatingGroup α) (Set.powersetCard α 4) where
  T s := (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by aesop)).isMulCommutative
    apply Subgroup.map_isMulCommutative
  is_conj g s := map_kleinFour_conj s.val s.prop g
  is_generator := by
    rw [eq_top_iff, ← closure_cycleType_eq_two_two_eq_top h5, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [SetLike.mem_coe]
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by
      simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype]
    · simp [hg]
    · simp [← sum_cycleType, hg]

/-- If `α` has at least 5 elements, but not 8,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 8)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  classical
  rw [or_iff_not_imp_left]
  intro hN
  have : IsPreprimitive (alternatingGroup α) (Set.powersetCard α 4) := by
    refine Set.powersetCard.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · apply lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff, ← commutator_alternatingGroup_eq_top
    (by simpa using hα)]
  apply (iwasawaStructure_four hα).commutator_le
  intro h
  simp_rw [Set.eq_univ_iff_forall, mem_fixedPoints] at h
  rw [← ne_eq, ← Subgroup.nontrivial_iff_ne_bot, Subgroup.nontrivial_iff_exists_ne_one] at hN
  obtain ⟨g, hgN, hg_ne⟩ := hN
  suffices ∃ s : Set.powersetCard α 4, g • s ≠ s by
    obtain ⟨s, hs⟩ := this
    apply hs
    rw [← Subgroup.mk_smul g hgN, h]
  contrapose! hg_ne
  replace hg_ne : (toPerm g : Perm (Set.powersetCard α 4)) = 1 := by
    ext1 s
    exact hg_ne s
  convert hg_ne
  rw [← Subtype.coe_inj]
  symm
  apply Set.powersetCard.mulAction_faithful
  · norm_num
  · have : CharZero ℕ∞ := instCharZeroENat
    rw [ENat.card_eq_coe_fintype_card, Nat.cast_ofNat,
          Nat.ofNat_lt_cast]
    simpa using hα

/-- If `α` has at least 5 elements,
then the only nontrivial normal subgroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top
    (hα : 5 ≤ Nat.card α)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_eight hα _ hnN
    rw [hα']
    simp
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
