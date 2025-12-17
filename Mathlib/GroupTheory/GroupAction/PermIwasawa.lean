/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

@[expose] public section

open scoped Pointwise

open MulAction

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

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α] [Finite α]

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
    rw [support_ofSubtype, Finset.mem_map] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [Set.mem_smul_set_iff_inv_smul_mem, ← hx]
    aesop
  · intro x
    simp only [Set.mem_smul_set_iff_inv_smul_mem]
    simpa using ofSubtype_apply_mem_iff_mem k _

variable [∀ s : Nat.Combination α 2, DecidablePred fun x ↦ x ∈ s]

theorem mem_rangeOfSubtype_iff
    {α : Type*} [DecidableEq α] [Fintype α] {p : α → Prop} [DecidablePred p]
    {g : Perm α} :
    g ∈ (ofSubtype : Perm (Subtype p) →* Perm α).range ↔
      (g.support : Set α) ⊆ setOf p := by
  constructor
  · rintro ⟨k, rfl⟩
    intro x hx
    simp only [support_ofSubtype, Finset.coe_map,
      Function.Embedding.subtype_apply, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simp
  · intro hg
    rw [← Equiv.Perm.ofSubtype_subtypePerm (f := g) (p := p) ?_ ?_]
    · simp
    · intro x
      by_cases hx : x ∈ (g.support : Set α)
      · simp only [Set.mem_setOf_eq.mp (hg hx)]
        rw [SetLike.mem_coe, ← mem_support_iff_of_commute (Commute.refl g) x,
          ← SetLike.mem_coe] at hx
        simp [Set.mem_setOf_eq.mp (hg hx)]
      · suffices g x = x by
          rw [this]
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
  simp only [mem_rangeOfSubtype_iff]
  simp only [SetLike.setOf_mem_eq, MulAut.smul_def, ← map_inv]
  rw [← Nat.Combination.coe_coe, Nat.Combination.coe_smul,
      Finset.coe_smul_finset, Nat.Combination.coe_coe]
  rw [MulAut.conj_apply, Equiv.Perm.support_conj]
  simp only [Finset.coe_map, coe_toEmbedding, coe_inv, Equiv.symm_image_subset]
  simp only [← Set.image_smul, Perm.smul_def]

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

open MulAction Equiv.Perm Equiv

variable {α : Type*} [DecidableEq α] [Fintype α]

def ofSubtype {α : Type*} [Fintype α] [DecidableEq α] {p : α → Prop} [DecidablePred p] :
    alternatingGroup (Subtype p) →* alternatingGroup α where
  toFun x := ⟨Perm.ofSubtype (p := p) x, by
    rw [mem_alternatingGroup, sign_ofSubtype, x.prop]⟩
  map_mul' x y := by simp
  map_one' := by simp

theorem mapOfSubtype {p : ℕ} (s : Nat.Combination α p) :
    Subgroup.map (ofSubtype : Perm (s : Finset α) →* Perm α) (alternatingGroup ↥(s : Finset α)) =
      (ofSubtype : Perm (s : Finset α) →* Perm α).range ⊓ (alternatingGroup α) := by
  ext k
  rw [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
  simp only [mem_alternatingGroup]
  refine ⟨fun ⟨x, hx, hk⟩ ↦ ?_, fun ⟨⟨x, hx⟩, hk⟩ ↦ ?_⟩
  · refine ⟨⟨x, hk⟩, ?_⟩
    rw [← hk, sign_ofSubtype]
    convert hx
  · refine ⟨x, ?_, hx⟩
    rw [← hx, sign_ofSubtype] at hk
    convert hk

lemma conj_map_subgroupOf {p : ℕ} (s : Nat.Combination α p) (g : alternatingGroup α) :
    ((alternatingGroup ↥((g • s : Nat.Combination α p) : Finset α)).map
      ofSubtype).subgroupOf (alternatingGroup α) =
    MulAut.conj g •
      ((alternatingGroup ↥(s : Finset α)).map ofSubtype).subgroupOf (alternatingGroup α) := by
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

def iwasawaStructure_three : IwasawaStructure (alternatingGroup α) (Nat.Combination α 3) where
  T s := (Subgroup.map ofSubtype (alternatingGroup s)).subgroupOf (alternatingGroup α)
  is_comm s := by
    suffices IsCyclic (alternatingGroup s) by
      let _ : CommGroup (alternatingGroup s) := IsCyclic.commGroup
      apply Subgroup.subgroupOf_isMulCommutative _
    apply isCyclic_of_prime_card (p := 3)
    have : Nontrivial s := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, s.prop]
      norm_num
    rw [nat_card_alternatingGroup, Nat.card_eq_finsetCard, s.prop]
    norm_num [Nat.factorial]
  is_conj g s := conj_map_subgroupOf s g
  is_generator := sorry

def iwasawaStructure_four : IwasawaStructure (alternatingGroup α) (Nat.Combination α 4) where
  T s := (Subgroup.map ofSubtype (kleinFour (α := s))).subgroupOf (alternatingGroup α)
  is_comm s := by
    suffices IsCyclic (alternatingGroup s) by
      let _ : CommGroup (alternatingGroup s) := IsCyclic.commGroup
      apply Subgroup.subgroupOf_isMulCommutative _
    apply isCyclic_of_prime_card (p := 3)
    have : Nontrivial s := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe, s.prop]
      norm_num
    rw [nat_card_alternatingGroup, Nat.card_eq_finsetCard, s.prop]
    norm_num [Nat.factorial]
  is_conj g s := conj_map_subgroupOf s g
  is_generator := sorry


end alternatingGroup


#exit

theorem Equiv.Perm.isCommutative_iff (α : Type*) [Finite α] :
    Std.Commutative (α := Equiv.Perm α) (· * ·) ↔ Nat.card α ≤ 2 := by
  have : Fintype α := Fintype.ofFinite α
  refine ⟨fun h ↦ ?_, fun hα ↦ ?_⟩
  · rw [← not_lt, Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    rintro ⟨a, b, c, hab, hac, hbc⟩
    apply hbc
    -- follows from applying `(a c) (a b) = (a b) (a c)` to `a`
    classical
    replace h := Equiv.ext_iff.mp (h.comm (swap a c) (swap a b)) a
    aesop
  · apply Monoid.isCommutative_of_natCard_le_2
    rw [Nat.card_perm]
    apply Nat.factorial_le hα

theorem Equiv.perm_is_nontrivial {α : Type*} [Finite α] :
    Nontrivial (Equiv.Perm α) ↔ 1 < Nat.card α := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, ← Fintype.one_lt_card_iff_nontrivial,
    Fintype.card_perm, Nat.one_lt_factorial]

theorem Monoid.isCommutative_of_natCard_le_2
    {M : Type*} [Monoid M] [Finite M] (hG : Nat.card M ≤ 2) :
    Std.Commutative (α := M) (· * ·) where
  comm a b := by
    by_cases ha : a = 1
    · simp [ha]
    by_cases hb : b = 1
    · simp [hb]
    suffices a = b by simp [this]
    rw [← not_lt] at hG
    contrapose hG
    have : Fintype M := Fintype.ofFinite M
    rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
    exact ⟨a, b, 1, hG, ha, hb⟩


