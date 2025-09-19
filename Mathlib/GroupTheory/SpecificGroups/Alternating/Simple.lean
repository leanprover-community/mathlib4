/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō, Aaron Anderson
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Simplicity of alternating groups

## Main statements

* `alternatingGroup.isSimpleGroup_five` shows that the alternating group on `Fin 5` is simple.
  The proof shows that the normal closure of any non-identity element of this group contains a
  3-cycle, this theorem is used in `alternatingGroup.isSimpleGroup_of_five_le` as the base case for
  induction.

* `alternatingGroup.isSimpleGroup_of_five_le` shows that the alternating group on `Fin n` for
  `5 ≤ n` is simple.

* `alternatingGroup.isSimpleGroup_iff_card_eq_three_or_card_ge_five` shows that the alternating
  group on `α` is simple if and only if `card α = 3 ∨ 5 ≤ card α`.
-/

open Equiv Equiv.Perm Subgroup Fintype MulAction Fin

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace alternatingGroup

lemma isSimpleGroup_of_card_eq_three (h3 : card α = 3) : IsSimpleGroup ↥(alternatingGroup α) := by
  haveI : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by rw [h3]; omega)
  haveI : Fact (Nat.Prime 3) := by decide
  apply isSimpleGroup_of_prime_card (p := 3)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, h3]; rfl

instance isSimpleGroup_three : IsSimpleGroup ↥(alternatingGroup (Fin 3)) := by
  apply isSimpleGroup_of_card_eq_three; simp

theorem not_isSimpleGroup_of_card_eq_four (h4 : card α = 4) :
    ¬IsSimpleGroup ↥(alternatingGroup α) := by
  rewrite [card_eq_nat_card] at h4
  simp_rw [isSimpleGroup_iff]
  set_option push_neg.use_distrib true in push_neg
  right
  refine ⟨kleinFour α, normal_kleinFour h4, ?ne_bot, ?ne_top⟩
  all_goals
    apply ne_of_apply_ne (fun S : Subgroup ↥(alternatingGroup α) => Nat.card ↥S)
    simp only [kleinFour_card_of_card_eq_four h4, Nat.card_unique, card_top,
      card_of_card_eq_four h4]
    decide

/-- Shows that $A_5$ is simple by taking an arbitrary non-identity element and showing by casework
on its cycle type that its normal closure is all of $A_5$.
This theorem is used in `alternatingGroup.isSimpleGroup_of_five_le` as the base case for
induction. -/
theorem isSimpleGroup_five : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
  ⟨fun H => by
    intro Hn
    refine or_not.imp id fun Hb => ?_
    rw [eq_bot_iff_forall] at Hb
    push_neg at Hb
    obtain ⟨⟨g, gA⟩, gH, g1⟩ : ∃ x : ↥(alternatingGroup (Fin 5)), x ∈ H ∧ x ≠ 1 := Hb
    -- `g` is a non-identity alternating permutation in a normal subgroup `H` of $A_5$.
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff] at gH
    refine eq_top_iff.2 (le_trans (ge_of_eq ?_) (normalClosure_le_normal gH))
    -- It suffices to show that the normal closure of `g` in $A_5$ is $A_5$.
    by_cases h2 : ∀ n ∈ g.cycleType, n = 2
    -- If the cycle decomposition of `g` consists entirely of swaps, then the cycle type is $(2,2)$.
    -- This means that it is conjugate to $(04)(13)$, whose normal closure is $A_5$.
    · rw [Ne, Subtype.ext_iff] at g1
      exact
        (isConj_swap_mul_swap_of_cycleType_two gA g1 h2).normalClosure_eq_top_of
          normalClosure_swap_mul_swap_five
    push_neg at h2
    obtain ⟨n, ng, n2⟩ : ∃ n : ℕ, n ∈ g.cycleType ∧ n ≠ 2 := h2
    -- `n` is the size of a non-swap cycle in the decomposition of `g`.
    have n2' : 2 < n := lt_of_le_of_ne (two_le_of_mem_cycleType ng) n2.symm
    have n5 : n ≤ 5 := le_trans ?_ g.support.card_le_univ
    -- We check that `2 < n ≤ 5`, so that `interval_cases` has a precise range to check.
    swap
    · obtain ⟨m, hm⟩ := Multiset.exists_cons_of_mem ng
      rw [← sum_cycleType, hm, Multiset.sum_cons]
      exact le_add_right le_rfl
    interval_cases n
    -- This breaks into cases `n = 3`, `n = 4`, `n = 5`.
    -- If `n = 3`, then `g` has a 3-cycle in its decomposition, so `g^2` is a 3-cycle.
    -- `g^2` is in the normal closure of `g`, so that normal closure must be $A_5$.
    · rw [eq_top_iff, ← (isThreeCycle_sq_of_three_mem_cycleType_five ng).alternating_normalClosure
        (by rw [card_fin])]
      refine normalClosure_le_normal ?_
      rw [Set.singleton_subset_iff, SetLike.mem_coe]
      have h := SetLike.mem_coe.1 (subset_normalClosure
        (G := alternatingGroup (Fin 5)) (Set.mem_singleton ⟨g, gA⟩))
      exact mul_mem h h
    · -- The case `n = 4` leads to contradiction, as no element of $A_5$ includes a 4-cycle.
      have con := mem_alternatingGroup.1 gA
      rw [sign_of_cycleType, cycleType_of_card_le_mem_cycleType_add_two (by decide) ng] at con
      have : Odd 5 := by decide
      simp [this] at con
    · -- If `n = 5`, then `g` is itself a 5-cycle, conjugate to `finRotate 5`.
      refine (isConj_iff_cycleType_eq.2 ?_).normalClosure_eq_top_of normalClosure_finRotate_five
      rw [cycleType_of_card_le_mem_cycleType_add_two (by decide) ng, cycleType_finRotate]⟩

attribute [local grind =]
  Cycle.nodup_coe_iff Finset.disjoint_insert_right Finset.disjoint_singleton_right support_inv in
/-- A key lemma to prove $A_n(5 \leq n)$ is simple. It shows that any nontrivial normal subgroup of
an alternating group on at least 6 elements contains a nontrivial element that fixes a specific
element. -/
theorem normal_subgroup_inf_stabilizer_ne_bot (h6 : 6 ≤ Fintype.card α)
    {H : Subgroup ↥(alternatingGroup α)} [iH : H.Normal] (nH : H ≠ ⊥) (a : α) :
    H ⊓ stabilizer ↥(alternatingGroup α) a ≠ ⊥ := by
  -- The proof method is based on: https://arbital.com/p/alternating_group_is_simple/
  simp_rw [← nontrivial_iff_ne_bot, nontrivial_iff_exists_ne_one, Subtype.exists,
    ne_eq, Subgroup.mk_eq_one] at nH ⊢
  simp_rw [mem_inf, mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def, and_assoc]
  obtain ⟨σ, hσ, hσH, hσ1⟩ := nH
  by_cases hσa : σ a = a
  case pos => exact ⟨σ, hσ, hσH, hσa, hσ1⟩
  clear hσ1
  rw [← ne_eq] at hσa
  suffices ∃ (τ : _) (hτ : τ ∈ alternatingGroup α), ⟨τ, hτ⟩ ∈ H ∧ τ a = σ a ∧ τ ≠ σ by
    obtain ⟨τ, hτ, hτH, hτσ, hnτσ⟩ := this
    rw [eq_comm, apply_eq_iff_eq_symm_apply, ← Perm.inv_def, eq_comm, ← mul_apply] at hτσ
    rw [ne_eq, eq_comm, ← inv_mul_eq_one, ← ne_eq] at hnτσ
    exact ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, mul_mem (inv_mem hσH) hτH, hτσ, hnτσ⟩
  have hσs : ¬σ.support ⊆ ({a, σ a} : Finset α) := by
    by_contra! hσs
    replace hσs := congr_arg Finset.card <| subset_antisymm hσs
      (by rwa [Finset.insert_subset_iff, Finset.singleton_subset_iff, apply_mem_support,
        and_self, mem_support])
    rw [Finset.card_pair hσa.symm, card_support_eq_two] at hσs
    rw [mem_alternatingGroup, hσs.sign_eq] at hσ
    contradiction
  simp_rw [Finset.not_subset, mem_support] at hσs
  obtain ⟨j, hjσ, hja⟩ := hσs
  have hxy := calc (2 : ℕ)
    _ = 6 - Multiset.card {a, σ a, j, σ j} := rfl
    _ ≤ card α - Multiset.card {a, σ a, j, σ j} := by omega
    _ ≤ card α - Finset.card {a, σ a, j, σ j} := by
      apply Nat.sub_le_sub_left
      convert Multiset.toFinset_card_le {a, σ a, j, σ j} using 2
      simp
    _ ≤ ({a, σ a, j, σ j}ᶜ : Finset α).card := by
      rw [Finset.card_compl]
  simp_rw [Finset.le_card_iff_exists_subset_card, Finset.card_eq_two,
    Finset.subset_compl_iff_disjoint_right] at hxy
  obtain ⟨_, hxys, x, y, hnxy, rfl⟩ := hxy
  have hcnd : (↑[j, x, y] : Cycle α).Nodup := by grind
  have hcnt : (↑[j, x, y] : Cycle α).Nontrivial := by
    simp [Cycle.nontrivial_coe_nodup_iff hcnd]
  let c := Cycle.formPerm (↑[j, x, y] : Cycle α) hcnd
  have ecs : c.support = {j, x, y} := by
    rw [Cycle.support_formPerm _ hcnd hcnt, Cycle.coe_toFinset]; simp
  have hcma : c ∈ alternatingGroup α := by
    rw [mem_alternatingGroup, Cycle.isCycle_formPerm _ hcnd hcnt |>.sign,
      Cycle.support_formPerm _ hcnd hcnt, Cycle.coe_toFinset, ← List.toFinset_eq hcnd]; rfl
  use c * σ * c⁻¹
  use mul_mem (mul_mem hcma hσ) (inv_mem hcma)
  use iH.conj_mem _ hσH ⟨c, hcma⟩
  use by
    have hanmcs : a ∉ (c⁻¹).support := by grind
    have hσanmcs : σ a ∉ c.support := by grind
    simp [notMem_support.mp hanmcs, notMem_support.mp hσanmcs]
  rw [DFunLike.ne_iff]; use j
  have ecij : c⁻¹ j = y := by
    simp_rw [c, ← Cycle.formPerm_reverse, Cycle.reverse_coe,
      show [j, x, y].reverse = [y, x, j] from rfl,
      Cycle.formPerm_apply_mem_eq_next (↑[y, x, j])
        (Cycle.nodup_reverse_iff.mpr hcnd) j (by simp)]
    simp only [Cycle.next, Cycle.ofList, Quot.hrecOn, Quot.recOn, Quot.rec]
    apply List.next_getLast_cons <;> [simp; skip; rfl; skip] <;> grind
  simp_rw [Perm.mul_apply, ecij]
  by_cases hσy : σ y ∈ c.support
  case neg =>
    rw [notMem_support.mp hσy, σ.injective.ne_iff]
    grind
  case pos =>
    intro ecσy
    rw [← apply_mem_support, ecσy, ecs] at hσy
    grind

attribute [local grind =] card_fin Fin.val_last Fin.lt_iff_val_lt_val in
/-- $A_n (5 \leq n)$ is simple. -/
theorem isSimpleGroup_of_five_le {n} (h5 : 5 ≤ n) :
    IsSimpleGroup ↥(alternatingGroup (Fin n)) := by
  induction n, h5 using Nat.le_induction with
  | base => exact isSimpleGroup_five
  | succ m hmn hm =>
    simp_rw [isSimpleGroup_iff, Classical.or_iff_not_imp_left, ← ne_eq]; constructor
    · rw [nontrivial_iff_three_le_card]; grind
    intro H hHn hHb
    simp_rw [(altCongrHom (finSuccAboveEquiv (last m))).isSimpleGroup_congr,
      (stabilizerEquiv _).symm.isSimpleGroup_congr, Subgroup.isSimpleGroup_iff,
      Classical.or_iff_not_imp_left, ← ne_eq] at hm
    replace hm := hm.2 (H ⊓ stabilizer _ (last m)) inf_le_right
      (by rewrite [inf_subgroupOf_right]; infer_instance)
      (normal_subgroup_inf_stabilizer_ne_bot (by grind) hHb _)
    rewrite [inf_eq_right, SetLike.le_def] at hm
    specialize @hm ⟨cycleRange ⟨2, by omega⟩, by simp⟩ (cycleRange_of_gt <| by grind)
    rwa [← SetLike.mem_coe, ← Set.singleton_subset_iff, normalClosure_subset_iff,
      IsThreeCycle.alternating_normalClosure (by grind) (by simp [IsThreeCycle]), top_le_iff] at hm

theorem isSimpleGroup_of_five_le_card (h5 : 5 ≤ card α) : IsSimpleGroup ↥(alternatingGroup α) := by
  obtain ⟨e⟩ := Fintype.truncEquivFin α |>.nonempty.map Equiv.altCongrHom
  rw [e.isSimpleGroup_congr]; exact isSimpleGroup_of_five_le h5

instance isSimpleGroup_add_five (n : ℕ) : IsSimpleGroup ↥(alternatingGroup (Fin (n + 5))) :=
  isSimpleGroup_of_five_le (Nat.le_add_left 5 n)

/-- $A_n$ is simple if and only if $n = 3$ or $5 \leq n$. -/
theorem isSimpleGroup_iff_card_eq_three_or_card_ge_five :
    IsSimpleGroup ↥(alternatingGroup α) ↔ card α = 3 ∨ 5 ≤ card α where
  mp hα := by
    grind [= isSimpleGroup_iff, = nontrivial_iff_three_le_card, ← not_isSimpleGroup_of_card_eq_four]
  mpr := Or.rec isSimpleGroup_of_card_eq_three isSimpleGroup_of_five_le_card

end alternatingGroup
