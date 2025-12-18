/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-! # The three Iwasawa structures on permutation and alternating groups

-/

@[expose] public section

open scoped Pointwise

open MulAction Equiv.Perm Equiv

/-- The action of `Equiv.Perm α` on `n.Combination α` is preprimitive
provided 1 ≤ n < #α and #α ≠ 2*n -/
theorem Nat.Combination_isPreprimitive
    {α : Type*} [DecidableEq α] [Fintype α]
    {n : ℕ} (h_one_le : 1 ≤ n) (hn : n < Fintype.card α)
    (hα : Fintype.card α ≠ 2 * n) :
    IsPreprimitive (Perm α) (n.Combination α) := by
  rcases Nat.eq_or_lt_of_le h_one_le with h_one | h_one_lt
  · -- n = 1 :
    rw [← h_one]
    have : IsPreprimitive (Perm α) α := inferInstance
    apply IsPreprimitive.of_surjective
      (Nat.Combination.mulActionHom_singleton_bijective (Perm α) α).surjective
  -- 1 < n
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    exact lt_trans h_one_lt hn
  have : IsPretransitive (Equiv.Perm α) (n.Combination α) :=
    Combination.isPretransitive α
    -- n.Combination_isPretransitive α
  have : Nontrivial (n.Combination α) := by
    apply Combination.nontrivial' h_one_le
    simpa using hn
  obtain ⟨s⟩ := this.to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]
  suffices stabilizer (Perm α) s = stabilizer (Perm α) (s : Set α) by
    rw [this]
    apply isCoatom_stabilizer
    · rwa [Combination.nonempty_iff]
    · simpa only [← Nat.Combination.coe_coe, ← Finset.coe_compl, Finset.coe_nonempty,
        ← Finset.card_compl_lt_iff_nonempty, compl_compl, Combination.card_eq]
    · contrapose hα
      rw [← Nat.card_eq_fintype_card, hα, Nat.mul_left_cancel_iff (by norm_num),
        ← Nat.Combination.coe_coe, Set.ncard_coe_finset, Combination.card_eq]
  ext g
  simp [mem_stabilizer_iff, ← Subtype.coe_inj, ← Finset.coe_inj]

theorem IsKleinFour.isMulCommutative {G : Type*} [Group G] [IsKleinFour G] :
    IsMulCommutative G where
  is_comm := {
    comm := mul_comm_of_exponent_two exponent_two
      }

theorem Subgroup.mem_smul_iff_inv_smul_mem
    {α β : Type*} [Group α] [Group β] [MulDistribMulAction α β]
    {a : α} {G : Subgroup β} {b : β} :
    b ∈ a • G ↔ a⁻¹ • b ∈ G := by
  simp only [← SetLike.mem_coe]
  rw [Subgroup.coe_pointwise_smul, Set.mem_smul_set_iff_inv_smul_mem]

theorem Subgroup.mem_inv_smul_iff_smul_mem
    {α β : Type*} [Group α] [Group β] [MulDistribMulAction α β]
    {a : α} {G : Subgroup β} {b : β} :
    b ∈ a⁻¹ • G ↔ a • b ∈ G := by
  simp only [← SetLike.mem_coe]
  rw [Subgroup.coe_pointwise_smul, Set.mem_inv_smul_set_iff]

theorem Finset.map_equiv_eq_smul {α : Type*} [DecidableEq α]
      (g : Equiv.Perm α) (s : Finset α) :
      Finset.map (Equiv.toEmbedding g) s = g • s := by
    ext x
    simp only [Finset.mem_map_equiv, ← Finset.inv_smul_mem_iff]
    rw [← Equiv.Perm.smul_def, ← Equiv.Perm.inv_def]

namespace Equiv.Perm

open Subgroup

variable {α : Type*} [DecidableEq α]

theorem disjoint_swap_swap [Fintype α]
    {x y z t : α} (h : [x, y, z, t].Nodup) :
    Disjoint (swap x y) (swap z t) := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  rw [(Equiv.Perm.support_swap_iff x y).mpr (by grind)]
  rw [(Equiv.Perm.support_swap_iff z t).mpr (by grind)]
  simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, not_or,
    Finset.disjoint_singleton_right]
  grind

theorem cycleType_swap_mul_swap' [Fintype α]
    {x y z t : α} (h : [x, y, z, t].Nodup) :
    ((swap x y) * (swap z t)).cycleType = {2, 2} := by
  rw [(disjoint_swap_swap h).cycleType_mul]
  rw [isSwap_iff_cycleType.mp ?_, isSwap_iff_cycleType.mp ?_]
  · simp
  · rw [Equiv.Perm.swap_isSwap_iff]
    grind
  · rw [Equiv.Perm.swap_isSwap_iff]
    grind

theorem sign_swap_mul_swap' [Fintype α]
    {x y z t : α} (h : [x, y, z, t].Nodup) :
    ((swap x y) * (swap z t)).sign = 1 := by
  rw [sign_of_cycleType, cycleType_swap_mul_swap' (by grind),
    ← Units.val_inj]
  norm_num

theorem support_swap_mul_swap' [Fintype α]
    {x y z t : α} (h : [x, y, z, t].Nodup) :
    ((swap x y) * (swap z t)).support = {x, y, z, t} := by
  apply le_antisymm
  · apply le_trans (Perm.support_mul_le _ _)
    apply sup_le
    · rw [support_swap (by grind)]
      simp
    · rw [support_swap (by grind)]
      simp only [Finset.le_eq_subset, Finset.subset_insert_iff, Finset.subset_singleton_iff]
      grind
  · apply Finset.insert_subset
    · simp only [mem_support, coe_mul, Function.comp_apply]; grind
    apply Finset.insert_subset
    · simp only [mem_support, coe_mul, Function.comp_apply]; grind
    apply Finset.insert_subset
    · simp only [mem_support, coe_mul, Function.comp_apply]; grind
    · simp only [Finset.singleton_subset_iff, mem_support, coe_mul, Function.comp_apply]; grind

example [Fintype α] (g : Perm α) (hg3 : g.IsThreeCycle) (a : α) :
    g.support = {a, g a, g (g a)} ↔ a ∈ g.support := by
  constructor
  · intro hg
    simp [hg]
  · intro ha
    symm
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.insert_subset ha
      apply Finset.insert_subset
      · rwa [Perm.apply_mem_support]
      simpa only [Finset.singleton_subset_iff, Perm.apply_mem_support]
    · rw [hg3.card_support]
      simp only [mem_support, ne_eq] at ha
      rw [Finset.card_insert_eq_ite, if_neg]
      · rw [Finset.card_insert_eq_ite, if_neg]
        · simp
        · simpa using Ne.symm ha
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        contrapose ha
        rcases ha with ha | ha
        · exact ha.symm
        · suffices (g ^ 3) a = a by
            simpa [pow_succ, ← ha] using this
          suffices g ^ 3 = 1 by simp [this]
          rw [← hg3.orderOf, pow_orderOf_eq_one]








example [Fintype α] (g : Perm α) (hg3 : g.IsThreeCycle) (a : α) :
    g = (swap a (g a)) * (swap (g a) (g (g a))) ↔
      a ∈ g.support := by
  constructor
  · intro hg
    rw [Perm.mem_support]
    intro hx
    simp only [hx, swap_self, mul_refl] at hg
    sorry
  intro hx
  ext x
  by_cases hx : x ∈ g.support
  · simp only [hG, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | (rfl | rfl)
    · simp [swap_apply_of_ne_of_ne (Ne.symm hx1) hx3, x2]
    · simp [swap_apply_of_ne_of_ne (Ne.symm hx3) hx2, x3]
    · simp [hx1x3]
  · rw [notMem_support.mp hx]
    simp only [hG, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    simp [Equiv.swap_apply_of_ne_of_ne hx.2.1 hx.2.2,
      Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.1]
  sorry

theorem closure_isCycleType22_eq_alternatingGroup
    [Fintype α] (h5 : 5 ≤ Nat.card α) :
    Subgroup.closure {g : Perm α | g.cycleType = {2, 2}} = alternatingGroup α := by
  apply le_antisymm
  · simp only [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp [mem_alternatingGroup, sign_of_cycleType, hg, ← Units.val_inj]
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating,
      Subgroup.closure_le]
    intro g hg3
    obtain ⟨x1, hx1'⟩ := hg3.isCycle.nonempty_support
    let x2 := g x1
    have hx2' : x2 ∈ g.support := by rwa [apply_mem_support]
    let x3 := g x2
    have hx3' : x3 ∈ g.support := by rwa [apply_mem_support]
    have hx1 : x2 ≠ x1 := by simpa using hx1'
    have hx2 : x3 ≠ x2 := by simpa using hx2'
    have hx1x3 : x1 = g x3 := by
      simp only [x3, x2, ← Perm.mul_apply]
      rw [← pow_two, ← pow_succ']
      simp [← hg3.orderOf, pow_orderOf_eq_one]
    have hx3 : x1 ≠ x3 := by simpa [hx1x3] using hx3'
    replace hG : g.support = {x1, x2, x3} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · grind
      · rw [hg3.card_support]
        grind
    have H : g = (swap x1 x2) * (swap x2 x3) := by
      ext x
      by_cases hx : x ∈ g.support
      · simp only [hG, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | (rfl | rfl)
        · simp [swap_apply_of_ne_of_ne (Ne.symm hx1) hx3, x2]
        · simp [swap_apply_of_ne_of_ne (Ne.symm hx3) hx2, x3]
        · simp [hx1x3]
      · rw [notMem_support.mp hx]
        simp only [hG, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        simp [Equiv.swap_apply_of_ne_of_ne hx.2.1 hx.2.2,
          Equiv.swap_apply_of_ne_of_ne hx.1 hx.2.1]
    have : ∃ x4 x5, x4 ∉ g.support ∧ x5 ∉ g.support ∧ x4 ≠ x5 := by
      simp only [← Finset.mem_compl]
      rw [← Finset.one_lt_card_iff]
      rw [← Nat.succ_le_iff, Nat.succ_eq_add_one]
      rw [← Nat.add_le_add_iff_right, Finset.card_compl_add_card]
      rwa [hg3.card_support, ← Nat.card_eq_fintype_card]
    obtain ⟨x4, x5, hx4', hx5', hx4x5⟩ := this
    let k1 := (swap x1 x2) * (swap x4 x5)
    let k2 := (swap x4 x5) * (swap x2 x3)
    have hk1 : k1.support = {x1, x2, x4, x5} := by
      exact support_swap_mul_swap' (by grind)
    have hk1' : k1.support.card = 4 := by grind
    have hk2 : k2.support = {x4, x5, x2, x3} := by
      simp only [k2]
      apply support_swap_mul_swap'
      grind
    have hk2' : k2.support.card = 4 := by grind
    have hk1s : k1 ∈ alternatingGroup α := by
      simp only [mem_alternatingGroup]
      exact sign_swap_mul_swap' (by grind)
    have hk2s : k2 ∈ alternatingGroup α := by
      simp only [mem_alternatingGroup]
      exact sign_swap_mul_swap' (by grind)
    have H : g = k1 * k2 := by
      simp [k1, k2, H, ← mul_assoc]
    rw [H]
    apply mul_mem <;>
    · apply Subgroup.subset_closure
      exact cycleType_swap_mul_swap' (by grind)


theorem mem_support_ofSubtype [Fintype α] {p : α → Prop}
    [DecidablePred p] (x : α) (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).support ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.support := by
  simp [support_ofSubtype]

lemma exists_Perm_smul_ofSubtype_eq_conj
    {α : Type*} [Finite α] [∀ s : Set α, DecidablePred fun x ↦ x ∈ s]
    (s : Set α) (k : Perm {x // x ∈ s}) (g : Perm α) :
    ∃ (x : Perm ↥(g • s)), ofSubtype x = g * ofSubtype k * g⁻¹ := by
  classical
  have : Fintype α := Fintype.ofFinite α
  use subtypePerm (g * ofSubtype k * g⁻¹) ?_
  · apply Equiv.Perm.ofSubtype_subtypePerm
    intro x hx
    replace hx : g⁻¹ • x ∈ (ofSubtype k).support := by aesop
    rw [mem_support_ofSubtype] at hx
    obtain ⟨hy, hx⟩ := hx
    rwa [Set.mem_smul_set_iff_inv_smul_mem]
  · intro x
    simp only [Set.mem_smul_set_iff_inv_smul_mem]
    simpa using ofSubtype_apply_mem_iff_mem k _

theorem Equiv.Perm.support_conj_eq_smul_support
    {α : Type*} [DecidableEq α] [Fintype α] (g k : Equiv.Perm α) :
    (g * k * g⁻¹).support = g • k.support := by
  rw [support_conj, Finset.map_equiv_eq_smul]

theorem Equiv.Perm.support_conj_eq_smul_support'
    {α : Type*} [DecidableEq α] [Fintype α] (g k : Equiv.Perm α) :
    (g⁻¹ * k * g).support = g⁻¹ • k.support := by
  nth_rewrite 2 [← inv_inv g]
  exact support_conj_eq_smul_support g⁻¹ k

variable [∀ s : Nat.Combination α 2, DecidablePred fun x ↦ x ∈ s]

theorem mem_rangeOfSubtype_iff
    {α : Type*} [DecidableEq α] [Fintype α] {p : α → Prop} [DecidablePred p]
    {g : Perm α} :
    g ∈ (ofSubtype : Perm (Subtype p) →* Perm α).range ↔
      (g.support : Set α) ⊆ setOf p := by
  constructor
  · rintro ⟨k, rfl⟩
    intro x
    simp only [Finset.mem_coe, mem_support_ofSubtype, Set.mem_setOf_eq]
    exact fun ⟨hx, _⟩ ↦ hx
  · intro hg
    rw [← Equiv.Perm.ofSubtype_subtypePerm (f := g) (p := p) ?_ ?_]
    · simp
    · intro x
      by_cases hx : x ∈ (g.support : Set α)
      · simp only [Set.mem_setOf_eq.mp (hg hx), iff_true]
        apply hg
        rwa [Finset.mem_coe, Equiv.Perm.apply_mem_support]
      · suffices g x = x by rw [this]
        simpa using hx
    · intro x hx
      apply hg
      simpa using hx

theorem conj_smul_rangeOfSubtype {α : Type*} [DecidableEq α] [Finite α] {p : ℕ}
    (g : Perm α) (s : Nat.Combination α p)
    [DecidablePred fun x ↦ x ∈ g • s] [DecidablePred fun x ↦ x ∈ s] :
    (ofSubtype : Perm { x // x ∈ ↑(g • s) } →*  Perm α).range
      = MulAut.conj g • (ofSubtype : Perm {x // x ∈ s} →* Perm α).range := by
  have : Fintype α := Fintype.ofFinite α
  ext k
  rw [Subgroup.mem_smul_iff_inv_smul_mem]
  simp only [mem_rangeOfSubtype_iff, SetLike.setOf_mem_eq, MulAut.smul_def, ← map_inv]
  rw [← Nat.Combination.coe_coe, Nat.Combination.coe_smul,
      Finset.coe_smul_finset, Nat.Combination.coe_coe]
  rw [MulAut.conj_apply, Equiv.Perm.support_conj]
  simp [← Set.image_smul, Perm.smul_def]

variable [Finite α]

/-- The Iwasawa structure of `Perm α` acting on `Nat.Combination α 2`. -/
def iwasawaStructure_two : IwasawaStructure (Perm α) (Nat.Combination α 2) where
  T s := (ofSubtype : Perm (s : Set α) →* Perm α).range
  is_comm s := by
    suffices IsCyclic (Perm s) by
      let _ : CommGroup (Perm s) := IsCyclic.commGroup
      apply MonoidHom.range_isMulCommutative
    apply isCyclic_of_prime_card (p := 2)
    rw [Nat.card_perm, Nat.card_eq_finsetCard, s.prop, Nat.factorial_two]
  is_conj g s := conj_smul_rangeOfSubtype g s
  is_generator := by
    rw [eq_top_iff]
    rw [← Equiv.Perm.closure_isSwap]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    obtain ⟨a, b, hab, rfl⟩ := hg
    set s : Nat.Combination α 2 := ⟨{a, b}, Finset.card_pair hab⟩
    apply Subgroup.mem_iSup_of_mem s
    exact ⟨swap ⟨a, by aesop⟩ ⟨b, by aesop⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

/-- If `α` has at least 5 elements, then the only nontrivial
normal sugroup of `Equiv.Perm α` is `alternatingGroup α`. -/
theorem Equiv.Perm.le_alternatingGroup
    {α : Type*} [DecidableEq α] [Fintype α] (hα : 5 ≤ Nat.card α)
    {N : Subgroup (Perm α)} (hnN : N.Normal) (ntN : Nontrivial N) :
    alternatingGroup α ≤ N := by
  rw [Nat.card_eq_fintype_card] at hα
  rw [← alternatingGroup.commutator_perm_eq hα]
  have : IsPreprimitive (Perm α) (Nat.Combination α 2) := by
    refine Nat.Combination_isPreprimitive (by norm_num) ?_ ?_
    · apply lt_of_lt_of_le (by norm_num) hα
    · intro h
      simp [h] at hα
  classical
  apply iwasawaStructure_two.commutator_le
  intro h
  obtain ⟨g, hgN, hg_ne⟩ := N.nontrivial_iff_exists_ne_one.mp ntN
  suffices ∃ s : Nat.Combination α 2, g • s ≠ s by
    obtain ⟨s, hs⟩ := this
    have := Set.mem_univ s
    rw [← h, mem_fixedPoints] at this
    apply hs
    rw [← Subgroup.mk_smul g hgN, this]
  contrapose! hg_ne
  replace hg_ne : (toPerm g : Perm (Nat.Combination α 2)) = 1 := by
    ext1 s
    exact hg_ne s
  rw [Nat.Combination.mulAction_faithful (n := 2)
    (G := Perm α) (α := α) (g := g)
    (by norm_num)
    (by rw [ENat.card_eq_coe_fintype_card, Nat.cast_ofNat,
          Nat.ofNat_lt_cast]
        apply le_trans (by norm_num) hα)] at hg_ne
  exact hg_ne

end Equiv.Perm

namespace alternatingGroup

open MulAction Equiv.Perm Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α]

/- def ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {p : α → Prop} [DecidablePred p] :
    alternatingGroup (Subtype p) →* alternatingGroup α where
  toFun x := ⟨Perm.ofSubtype (p := p) x, by
    rw [mem_alternatingGroup, sign_ofSubtype, x.prop]⟩
  map_mul' x y := by simp
  map_one' := by simp
-/

-- The `convert` is bizarre
def ofSubtype {p : ℕ} (s : Nat.Combination α p) :
    alternatingGroup s →* alternatingGroup α where
  toFun x := ⟨Perm.ofSubtype (x : Perm s), by
    have := mem_alternatingGroup.mp x.prop
    rw [mem_alternatingGroup, sign_ofSubtype]
    convert this⟩
  map_mul' := by simp
  map_one' := by simp

theorem mapOfSubtype {p : ℕ} (s : Nat.Combination α p) :
    (alternatingGroup ↥(s : Finset α)).map (Perm.ofSubtype : Perm (s : Finset α) →* Perm α) =
      (Perm.ofSubtype : Perm (s : Finset α) →* Perm α).range ⊓ (alternatingGroup α) := by
  ext k
  rw [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
  simp only [mem_alternatingGroup]
  refine ⟨fun ⟨x, hx, hk⟩ ↦ ?_, fun ⟨⟨x, hx⟩, hk⟩ ↦ ?_⟩
  · refine ⟨⟨x, hk⟩, ?_⟩
    rw [← hk, sign_ofSubtype]
    -- exact doesn't work!
    convert hx
  · refine ⟨x, ?_, hx⟩
    rw [← hx, sign_ofSubtype] at hk
    convert hk

lemma conj_map_subgroupOf {p : ℕ} (s : Nat.Combination α p) (g : alternatingGroup α) :
    ((alternatingGroup ↥((g • s : Nat.Combination α p) : Finset α)).map
      Perm.ofSubtype).subgroupOf (alternatingGroup α) =
    MulAut.conj g •
      ((alternatingGroup ↥(s : Finset α)).map Perm.ofSubtype).subgroupOf (alternatingGroup α) := by
  classical
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_smul_iff_inv_smul_mem]
  simp only [mapOfSubtype, Subgroup.mem_inf]
  simp only [Subgroup.mk_smul]
  simp only [MulAut.smul_def, MulAut.inv_apply,
    MulAut.conj_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [← MulAut.conj_symm_apply, ← MulAut.inv_apply, ← MulAut.smul_def]
  rw [← Subgroup.mem_smul_iff_inv_smul_mem, ← conj_smul_rangeOfSubtype]
  apply and_congr
  · convert Iff.rfl
  · simp only [mem_alternatingGroup, MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
    simp only [sign_mul, sign_inv, mul_right_comm]
    simp

theorem mem_range_ofSubtype {p : ℕ} (s : Nat.Combination α p) (k : alternatingGroup α) :
    k ∈ (ofSubtype s).range ↔ (k : Perm α).support ⊆ s := by
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    intro x hx
    simp only [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk,
      support_ofSubtype] at hx
    aesop
  · intro hk
    rcases k with ⟨k, hk'⟩
    simp only at hk
    simp only [ofSubtype, MonoidHom.mem_range, MonoidHom.coe_mk, OneHom.coe_mk, ← Subtype.coe_inj,
      Subtype.exists, mem_alternatingGroup, exists_prop]
    suffices k ∈ (Perm.ofSubtype : Perm s →* Perm α).range by
      obtain ⟨k, rfl⟩ := this
      rw [mem_alternatingGroup, sign_ofSubtype] at hk'
      refine ⟨k, ?_, rfl⟩
      convert hk'
    rw [mem_rangeOfSubtype_iff]
    simpa using hk

theorem range_ofSubtype_conj {p : ℕ} (s : Nat.Combination α p) (g : alternatingGroup α) :
    (ofSubtype (g • s)).range = MulAut.conj g • (ofSubtype s).range := by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  rw [Subgroup.mem_smul_iff_inv_smul_mem]
  simp only [mem_range_ofSubtype]
  simp only [mk_smul, Nat.Combination.coe_smul, MulAut.smul_def, MulAut.inv_apply,
    MulAut.conj_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [Equiv.Perm.support_conj_eq_smul_support', Finset.subset_smul_finset_iff]

theorem closure_isThreeCycles_eq_top :
    Subgroup.closure
      {g : alternatingGroup α | Equiv.Perm.IsThreeCycle (g : Equiv.Perm α)} = ⊤ := by
  apply Subgroup.map_injective (alternatingGroup α).subtype_injective
  rw [MonoidHom.map_closure]
  suffices (alternatingGroup α).subtype ''
    { g : alternatingGroup α | (g : Perm α).IsThreeCycle } =
      { g : Perm α | IsThreeCycle g} by
    aesop
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · exact fun hg ↦ ⟨⟨g, hg.mem_alternatingGroup⟩, by simpa⟩

theorem range_ofSubtype_three_is_generator :
    (iSup fun s : Nat.Combination α 3 ↦ (ofSubtype s).range) = ⊤ := by
  rw [eq_top_iff, ← closure_isThreeCycles_eq_top, Subgroup.closure_le]
  intro g hg
  apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
  rw [mem_range_ofSubtype]

theorem closure_isCycleType22_eq_top (h5 : 5 ≤ Nat.card α) :
    Subgroup.closure
      {g : alternatingGroup α | (g : Equiv.Perm α).cycleType = {2, 2} } = ⊤ := by
  apply Subgroup.map_injective (alternatingGroup α).subtype_injective
  rw [MonoidHom.map_closure]
  suffices (alternatingGroup α).subtype ''
    { g : alternatingGroup α | (g : Perm α).cycleType = {2, 2} } =
      { g : Perm α | g.cycleType = {2, 2} } by
    rw [this, Perm.closure_isCycleType22_eq_alternatingGroup h5]
    aesop
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro hg
    refine ⟨⟨g, ?_⟩, by simpa⟩
    simp only [Set.mem_setOf_eq] at hg
    simp [sign_of_cycleType, hg, ← Units.val_inj]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Nat.Combination α 3`. -/
def iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Nat.Combination α 3) where
  T s := (ofSubtype s).range
  is_comm s := by
    suffices IsCyclic (alternatingGroup s) by
      let _ : CommGroup (alternatingGroup s) := IsCyclic.commGroup
      exact MonoidHom.range_isMulCommutative (ofSubtype s)
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

theorem mem_map_kleinFour_ofSubtype (s : Nat.Combination α 4) (k : alternatingGroup α) :
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
    rw [mem_map]
    rw [← mem_range_ofSubtype] at hk
    obtain ⟨k, rfl⟩ := hk
    simp only [ofSubtype, MonoidHom.coe_mk, OneHom.coe_mk, cycleType_ofSubtype] at hk'
    use k
    refine ⟨?_, rfl⟩
    rw [← SetLike.mem_coe, coe_kleinFour_of_card_eq_four hs,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
    simp only [map_eq_one_iff _ ofSubtype_injective, OneMemClass.coe_eq_one] at hk'
    convert hk'

theorem map_kleinFour_conj (s : Nat.Combination α 4) (g : alternatingGroup α) :
    (kleinFour _).map (ofSubtype (g • s)) =
        MulAut.conj g • ((kleinFour s).map (ofSubtype s)) := by
  rcases g with ⟨g, hg⟩
  ext ⟨k, hk⟩
  rw [Subgroup.mem_smul_iff_inv_smul_mem]
  simp only [mem_map_kleinFour_ofSubtype]
  simp only [mk_smul, Nat.Combination.coe_smul, MulAut.smul_def, MulAut.inv_apply,
    MulAut.conj_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [Equiv.Perm.support_conj_eq_smul_support', Finset.subset_smul_finset_iff]
  apply and_congr Iff.rfl
  apply or_congr
  · simp [mul_eq_one_iff_inv_eq']
  · nth_rewrite 2 [← inv_inv g]
    rw [cycleType_conj]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Nat.Combination α 4`,
provided `α` has at least 5 elements. -/
def iwasawaStructure_four (h5 : 5 ≤ Nat.card α) :
    IwasawaStructure (alternatingGroup α) (Nat.Combination α 4) where
  T s := (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by aesop)).isMulCommutative
    apply map_isMulCommutative
  is_conj g s := map_kleinFour_conj s g
  is_generator := by
    rw [eq_top_iff, ← closure_isCycleType22_eq_top h5, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    simp only [SetLike.mem_coe]
    apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, by
      simp [← sum_cycleType, hg]⟩
    rw [mem_map_kleinFour_ofSubtype]
    simp [hg]

end alternatingGroup
