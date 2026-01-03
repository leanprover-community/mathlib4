/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module


public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.Perm.MaximalSubgroups
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-! # The alternating group is simple

* `Equiv.Perm.iwasawaStructure_two`:
  the natural `IwasawaStructure` of `Equiv.Perm α` acting on `Nat.Combination α 2`
  Its commutative subgroups consist of the permutations with support
  in a given element of `Nat.Combination α 2`.
  They are cyclic of order 2.

* `alternatingGroup_of_le_of_normal`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup
  of `Equiv.Perm α` contains the alternating group.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Nat.Combination α 3`

  Its commutative subgroups consist of the permutations with support
  in a given element of `Nat.Combination α 2`.
  They are cyclic of order 3.

* `alternatingGroup.iwasawaStructure_three`:
  the natural `IwasawaStructure` of `alternatingGroup α` acting on `Nat.Combination α 4`

  Its commutative subgroups consist of the permutations of
  cycleType (2, 2) with support in a given element of `Nat.Combination α 2`.
  They have order 4 and exponent 2 (`IsKleinFour`).

* `alternatingGroup.normal_subgroup_eq_bot_or_eq_top`:
  If `α` has at least 5 elements, then a nontrivial normal subgroup of `alternatingGroup` is `⊤`.

* `alternatingGroup.isSimpleGroup`:
  If `α` has at least 5 elements, then `alternatingGroup α`
  is a simple group.

-/


open scoped Pointwise

open MulAction Equiv.Perm Equiv

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α]

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
  simp [support_conj, Finset.smul_finset_def, Finset.map_eq_image]

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
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_rangeOfSubtype_iff, SetLike.setOf_mem_eq, MulAut.smul_def, ← map_inv]
  rw [← Nat.Combination.coe_coe, Nat.Combination.coe_smul,
      Finset.coe_smul_finset, Nat.Combination.coe_coe]
  rw [MulAut.conj_apply, Equiv.Perm.support_conj]
  simp [← Set.image_smul, Perm.smul_def]

variable [Finite α]

/-- The Iwasawa structure of `Perm α` acting on `Nat.Combination α 2`. -/
@[expose] public def iwasawaStructure_two : IwasawaStructure (Perm α) (Nat.Combination α 2) where
  T s := (ofSubtype : Perm (s : Set α) →* Perm α).range
  is_comm s := by
    suffices IsCyclic (Perm s) by
      let _ : CommGroup (Perm s) := IsCyclic.commGroup
      apply MonoidHom.range_isMulCommutative
    apply isCyclic_of_prime_card (p := 2)
    rw [Nat.card_perm, Nat.card_eq_finsetCard, s.prop, Nat.factorial_two]
  is_conj g s := conj_smul_rangeOfSubtype g s
  is_generator := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    intro g hg
    obtain ⟨a, b, hab, rfl⟩ := hg
    let s : Nat.Combination α 2 := ⟨{a, b}, Finset.card_pair hab⟩
    apply Subgroup.mem_iSup_of_mem s
    exact ⟨swap ⟨a, by aesop⟩ ⟨b, by aesop⟩, Equiv.Perm.ofSubtype_swap_eq _ _⟩

/-- If `α` has at least 5 elements, then the only nontrivial
normal sugroup of `Equiv.Perm α` is `alternatingGroup α`. -/
public theorem alternatingGroup_of_le_of_normal
    {α : Type*} [DecidableEq α] [Fintype α] (hα : 5 ≤ Nat.card α)
    {N : Subgroup (Perm α)} (hnN : N.Normal) (ntN : Nontrivial N) :
    alternatingGroup α ≤ N := by
  rw [Nat.card_eq_fintype_card] at hα
  rw [← alternatingGroup.commutator_perm_eq hα]
  rw [← Nat.card_eq_fintype_card] at hα
  have : IsPreprimitive (Perm α) (Nat.Combination α 2) := by
    apply Nat.Combination.isPreprimitive_Perm α (by norm_num)
      (lt_of_lt_of_le (by norm_num) hα)
    intro h
    rw [h] at hα
    simp at hα
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
        simpa using le_trans (by norm_num) hα)] at hg_ne
  exact hg_ne

end Equiv.Perm

namespace alternatingGroup

-- open MulAction Equiv.Perm Equiv Finset Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α]

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
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mapOfSubtype, Subgroup.mem_inf]
  simp only [Subgroup.mk_smul]
  simp only [MulAut.smul_def, MulAut.inv_apply,
    MulAut.conj_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [← MulAut.conj_symm_apply, ← MulAut.inv_apply, ← MulAut.smul_def]
  rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← conj_smul_rangeOfSubtype]
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
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_range_ofSubtype]
  simp only [Subgroup.mk_smul, Nat.Combination.coe_smul, MulAut.smul_def, MulAut.inv_apply,
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

theorem closure_isCycleType22_eq_top (h5 : 5 ≤ Nat.card α) :
    Subgroup.closure
      {g : alternatingGroup α | (g : Perm α).cycleType = {2, 2} } = ⊤ := by
  apply Subgroup.map_injective (alternatingGroup α).subtype_injective
  rw [MonoidHom.map_closure]
  suffices (alternatingGroup α).subtype ''
    { g : alternatingGroup α | (g : Perm α).cycleType = {2, 2} } =
      { g : Perm α | g.cycleType = {2, 2} } by
    rw [this, Perm.closure_cycleType_eq_2_2_eq_alternatingGroup h5]
    aesop
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩; exact hk
  · intro hg
    refine ⟨⟨g, ?_⟩, by simpa⟩
    simp only [Set.mem_setOf_eq] at hg
    simp [sign_of_cycleType, hg, ← Units.val_inj]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Nat.Combination α 3`. -/
@[expose] public
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

/-- If `α` has at least 5 elements, but not 6,
then the only nontrivial normal sugroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_6
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 6)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  rw [Classical.or_iff_not_imp_left]
  intro hN
  rw [Nat.card_eq_fintype_card] at hα
  have : IsPreprimitive (alternatingGroup α) (Nat.Combination α 3) := by
    refine Nat.Combination.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · apply lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff]
  rw [← commutator_alternatingGroup_eq_top hα]
  apply iwasawaStructure_three.commutator_le
  intro h
  rw [← ne_eq, ← Subgroup.nontrivial_iff_ne_bot, Subgroup.nontrivial_iff_exists_ne_one] at hN
  obtain ⟨g, hgN, hg_ne⟩ := hN
  suffices ∃ s : Nat.Combination α 3, g • s ≠ s by
    obtain ⟨s, hs⟩ := this
    have := Set.mem_univ s
    rw [← h, mem_fixedPoints] at this
    apply hs
    rw [← Subgroup.mk_smul g hgN, this]
  contrapose! hg_ne
  replace hg_ne : (toPerm g : Perm (Nat.Combination α 3)) = 1 := by
    ext1 s
    exact hg_ne s
  rw [Nat.Combination.mulAction_faithful (n := 3)
    (G := alternatingGroup α) (α := α) (g := g)
    (by norm_num)
    (by rw [ENat.card_eq_coe_fintype_card, Nat.cast_ofNat,
          Nat.ofNat_lt_cast]
        apply le_trans (by norm_num) hα)] at hg_ne
  ext x
  simp only [Perm.ext_iff, toPerm_apply, Subgroup.mk_smul g.val g.prop, Perm.smul_def] at hg_ne
  simp [hg_ne]

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
    rw [Subgroup.mem_map]
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
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_map_kleinFour_ofSubtype]
  simp only [Subgroup.mk_smul, Nat.Combination.coe_smul, MulAut.smul_def, MulAut.inv_apply,
    MulAut.conj_symm_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
  rw [Equiv.Perm.support_conj_eq_smul_support', Finset.subset_smul_finset_iff]
  apply and_congr Iff.rfl
  apply or_congr
  · simp [mul_eq_one_iff_inv_eq']
  · nth_rewrite 2 [← inv_inv g]
    rw [cycleType_conj]

/-- The Iwasawa structure of `alternatingGroup α` acting on `Nat.Combination α 4`,
provided `α` has at least 5 elements. -/
@[expose] public def iwasawaStructure_four (h5 : 5 ≤ Nat.card α) :
    IwasawaStructure (alternatingGroup α) (Nat.Combination α 4) where
  T s := (kleinFour s).map (ofSubtype s)
  is_comm s := by
    have : IsMulCommutative (kleinFour s) :=
      (kleinFour_isKleinFour (by aesop)).isMulCommutative
    apply Subgroup.map_isMulCommutative
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

/-- If `α` has at least 5 elements, but not 8,
then the only nontrivial normal sugroup of `alternatingGroup α`
is `⊤`. -/
theorem normal_subgroup_eq_bot_or_eq_top_of_card_ne_8
    (hα : 5 ≤ Nat.card α) (hα' : Nat.card α ≠ 8)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  rw [Classical.or_iff_not_imp_left]
  intro hN
  rw [Nat.card_eq_fintype_card] at hα
  have : IsPreprimitive (alternatingGroup α) (Nat.Combination α 4) := by
    refine Nat.Combination.isPreprimitive_alternatingGroup (by norm_num) ?_ ?_
    · apply lt_of_lt_of_le (by norm_num) hα
    · simpa using hα'
  rw [eq_top_iff]
  rw [← commutator_alternatingGroup_eq_top hα]
  rw [← Nat.card_eq_fintype_card] at hα
  apply (iwasawaStructure_four hα).commutator_le
  intro h
  rw [← ne_eq, ← Subgroup.nontrivial_iff_ne_bot, Subgroup.nontrivial_iff_exists_ne_one] at hN
  obtain ⟨g, hgN, hg_ne⟩ := hN
  suffices ∃ s : Nat.Combination α 4, g • s ≠ s by
    obtain ⟨s, hs⟩ := this
    have := Set.mem_univ s
    rw [← h, mem_fixedPoints] at this
    apply hs
    rw [← Subgroup.mk_smul g hgN, this]
  contrapose! hg_ne
  replace hg_ne : (toPerm g : Perm (Nat.Combination α 4)) = 1 := by
    ext1 s
    exact hg_ne s
  rw [Nat.Combination.mulAction_faithful (n := 4)
    (G := alternatingGroup α) (α := α) (g := g)
    (by norm_num)
    (by rw [ENat.card_eq_coe_fintype_card, Nat.cast_ofNat,
          Nat.ofNat_lt_cast]
        simpa using hα)] at hg_ne
  ext x
  simp only [Perm.ext_iff, toPerm_apply, Subgroup.mk_smul g.val g.prop, Perm.smul_def] at hg_ne
  simp [hg_ne]

/-- If `α` has at least 5 elements,
then the only nontrivial normal sugroup of `alternatingGroup α`
is `⊤`. -/
public theorem normal_subgroup_eq_bot_or_eq_top
    (hα : 5 ≤ Nat.card α)
    {N : Subgroup (alternatingGroup α)} (hnN : N.Normal) :
    N = ⊥ ∨ N = ⊤ := by
  by_cases hα' : Nat.card α = 6
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_8 hα _ hnN
    rw [hα']
    simp
  · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_6 hα hα' hnN

/-- When `α` has at least 5 elements, then `alternatingGroup α` is a simple group. -/
public theorem isSimpleGroup (hα : 5 ≤ Nat.card α) :
    IsSimpleGroup (alternatingGroup α) where
  exists_pair_ne := by
    suffices Nontrivial (alternatingGroup α) by
      apply Nontrivial.exists_pair_ne
    refine nontrivial_of_three_le_card ?_
    simpa using le_trans (by norm_num) hα
  eq_bot_or_eq_top_of_normal H hH := by
    by_cases hα' : Nat.card α = 6
    · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_8 hα _ hH
      rw [hα']
      simp
    · apply normal_subgroup_eq_bot_or_eq_top_of_card_ne_6 hα hα' hH

end alternatingGroup
