/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-! # The three Iwasawa structures on permutation and alternating groups

-/

@[expose] public section

open scoped Pointwise

open MulAction

theorem IsKleinFour.isMulCommutative {G : Type*} [Group G] [IsKleinFour G] :
    IsMulCommutative G where
  is_comm := {
    comm := mul_comm_of_exponent_two exponent_two
      }

theorem Subgroup.map_closure_eq {G H : Type*} [Group G] [Group H]
    (f : H →* G) (s : Set H) :
    Subgroup.map f (Subgroup.closure s) = Subgroup.closure (Set.image f s) := by
  exact MonoidHom.map_closure f s
  symm
  apply Subgroup.closure_eq_of_le
  · rintro g ⟨k, hk, rfl⟩
    exact ⟨k, Subgroup.subset_closure hk, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro g hg
    simp only [Subgroup.coe_comap, Set.mem_preimage, SetLike.mem_coe]
    exact subset_closure (Set.mem_image_of_mem f hg)

theorem Subgroup.closure_subgroupOf_eq {G : Type_} [Group G]
    (N : Subgroup G) (s : Set G) (hs : s ≤ ↑N) :
    Subgroup.closure (N.subtype ⁻¹' s) = (Subgroup.closure s).subgroupOf N := by
  simp only [Subgroup.subgroupOf]
  apply Subgroup.map_injective (subtype_injective N)
  rw [MonoidHom.map_closure]
  suffices N.subtype '' (N.subtype ⁻¹' s) = s by aesop
  aesop


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

variable {α : Type*} [DecidableEq α] [Finite α]

theorem mem_support_ofSubtype
    {α : Type*} [DecidableEq α] [Fintype α] {p : α → Prop}
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

theorem closure_isThreeCycle_eq_top :
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
  rw [eq_top_iff, ← closure_isThreeCycle_eq_top, Subgroup.closure_le]
  intro g hg
  apply Subgroup.mem_iSup_of_mem ⟨(g : Perm α).support, hg.card_support⟩
  rw [mem_range_ofSubtype]

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
    rw [eq_top_iff, ← closure_isThreeCycle_eq_top, Subgroup.closure_le]
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
    rw [eq_top_iff, ← closure_isThreeCycle_eq_top, Subgroup.closure_le]
    intro g
    rcases g with ⟨g, hg⟩
    intro (hg3 : g.IsThreeCycle)
    let t := g.support
    obtain ⟨x1, hx1'⟩ := hg3.isCycle.nonempty_support
    let x2 := g x1
    have hx2' : x2 ∈ g.support := by rwa [apply_mem_support]
    let x3 := g x2
    have hx3' : x3 ∈ g.support := by rwa [apply_mem_support]
    have hx1 : x2 ≠ x1 := by simpa using hx1'
    have hx2 : x3 ≠ x2 := by simpa using hx2'
    have hx3 : x1 ≠ x3 := by
      suffices x1 = g x3 by simpa [this] using hx3'
      simp only [x3, x2, ← Perm.mul_apply]
      rw [← pow_two, ← pow_succ']
      simp [← hg3.orderOf, pow_orderOf_eq_one]
    have H : g = (swap x1 x2) * (swap x2 x3) := by
      sorry
    have H1 : g.support = {x1, x2, x3} := sorry
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
      apply le_antisymm
      · simp only [k1]
        apply le_trans (Perm.support_mul_le _ _)
        apply sup_le
        · simp [support_swap (Ne.symm hx1)]
        · rw [support_swap hx4x5]
          simp only [Finset.le_eq_subset, Finset.subset_insert_iff, Finset.subset_singleton_iff]
          grind
      · apply Finset.insert_subset
        · simp [k1]; grind
        apply Finset.insert_subset
        · simp [k1]; grind
        apply Finset.insert_subset
        · simp [k1]; grind
        · simp [k1]; grind
    have hk1' : k1.support.card = 4 := by grind
    have hk2 : k2.support = {x2, x3, x4, x5} := by
      apply le_antisymm
      · simp only [k2]
        apply le_trans (Perm.support_mul_le _ _)
        apply sup_le
        · rw [support_swap hx4x5]
          simp only [Finset.le_eq_subset, Finset.subset_insert_iff, Finset.subset_singleton_iff]
          grind
        · simp [support_swap (Ne.symm hx2)]
      · apply Finset.insert_subset
        · simp [k2]; grind
        apply Finset.insert_subset
        · simp [k2]; grind
        apply Finset.insert_subset
        · simp [k2]; grind
        · simp [k2]; grind
    have hk2' : k2.support.card = 4 := by grind
    have hk1s : k1 ∈ alternatingGroup α := by
      simp only [mem_alternatingGroup, sign_mul, sign_swap', mul_ite, mul_one, mul_neg, k1]
      rw [if_neg hx4x5, if_neg (Ne.symm hx1)]
      simp
    have hk2s : k2 ∈ alternatingGroup α := by
      simp only [mem_alternatingGroup, sign_mul, sign_swap', mul_ite, mul_one, mul_neg, k2]
      rw [if_neg hx4x5, if_neg (Ne.symm hx2)]
      simp
    have H : (⟨g, hg⟩ : alternatingGroup α) = ⟨k1, hk1s⟩ * ⟨k2, hk2s⟩ := by
      rw [← Subtype.coe_inj, MulMemClass.mk_mul_mk]
      simp [k1, k2, H, ← mul_assoc]
    rw [H]
    apply mul_mem
    · apply Subgroup.mem_iSup_of_mem ⟨k1.support, hk1'⟩
      rw [mem_map_kleinFour_ofSubtype]
      suffices k1.cycleType = {2, 2} by simp [this]
      sorry
    · apply Subgroup.mem_iSup_of_mem ⟨k2.support, hk2'⟩
      rw [mem_map_kleinFour_ofSubtype]
      suffices k2.cycleType = {2, 2} by simp [this]
      sorry


end alternatingGroup
