/-
Copyright (c) 2025. Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.MultiplePrimitivity

/-! # Theorems of Jordan

A proof of theorems of Jordan regarding primitive permutation groups.

This mostly follows the book [Wielandt, *Finite permutation groups*][Wielandt-1964].

- `MulAction.IsPreprimitive.is_two_pretransitive` and
  `MulAction.IsPreprimitive.is_two_preprimitive` are technical lemmas
  that prove 2-pretransitivity / 2-preprimitivity for some group
  primitive actions given the transitivity / primitivity of
  `ofFixingSubgroup G s` (Wielandt, 13.1)

- `MulAction.IsPreprimitive.isMultiplyPreprimitive`:
  A multiple preprimitivity criterion of Jordan (1871) for a preprimitive
  action: the hypothesis is the preprimitivity of the `SubMulAction`
  of `fixingSubgroup s` on `ofFixingSubgroup G s` (Wielandt, 13.2)

- `Equiv.Perm.eq_top_of_isPreprimitive_of_isSwap_mem` :
  a primitive subgroup of a permutation group that contains a
  swap is equal to the full permutation group (Wielandt, 13.3)

- `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem` :
  a primitive subgroup of a permutation group that contains a 3-cycle
  contains the alternating group (Wielandt, 13.3)

## TODO

- Prove `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`:
  a primitive subgroup of a permutation group that contains
  a cycle of *prime* order contains the alternating group (Wielandt, 13.9).

- Prove the stronger versions of the technical lemmas of Jordan (Wielandt, 13.1').

-/

open MulAction SubMulAction Subgroup

open scoped Pointwise

section Jordan

variable {G α : Type*} [Group G] [MulAction G α]

/-- In a 2-transitive action, the normal closure of stabilizers is the full group. -/
theorem normalClosure_of_stabilizer_eq_top (hsn' : 2 < ENat.card α)
    (hG' : IsMultiplyPretransitive G α 2) {a : α} :
    normalClosure ((stabilizer G a) : Set G) = ⊤ := by
  have : IsPretransitive G α := by
    rw [← is_one_pretransitive_iff]
    exact isMultiplyPretransitive_of_le' (one_le_two) (le_of_lt hsn')
  have : Nontrivial α := by
    rw [← ENat.one_lt_card_iff_nontrivial]
    exact lt_trans (by norm_num) hsn'
  have hGa : IsCoatom (stabilizer G a) := by
    rw [isCoatom_stabilizer_iff_preprimitive]
    exact isPreprimitive_of_is_two_pretransitive hG'
  apply hGa.right
  -- Remains to prove: (stabilizer G a) < Subgroup.normalClosure (stabilizer G a)
  constructor
  · apply le_normalClosure
  · intro hyp
    have : Nontrivial (ofStabilizer G a) := by
      rw [← ENat.one_lt_card_iff_nontrivial]
      apply lt_of_add_lt_add_right
      rwa [ENat_card_ofStabilizer_add_one_eq]
    rw [nontrivial_iff] at this
    obtain ⟨b, c, hbc⟩ := this
    have : IsPretransitive (stabilizer G a) (ofStabilizer G a) := by
      rw [← is_one_pretransitive_iff]
      rwa [← ofStabilizer.isMultiplyPretransitive]
    -- get g ∈ stabilizer G a, g • b = c,
    obtain ⟨⟨g, hg⟩, hgbc⟩ := exists_smul_eq (stabilizer G a) b c
    apply hbc
    rw [← SetLike.coe_eq_coe] at hgbc ⊢
    obtain ⟨h, hinvab⟩ := exists_smul_eq G (b : α) a
    rw [eq_comm, ← inv_smul_eq_iff] at hinvab
    rw [← hgbc, SetLike.val_smul, ← hinvab, inv_smul_eq_iff, eq_comm]
    simp only [subgroup_smul_def, smul_smul, ← mul_assoc, ← mem_stabilizer_iff]
    exact hyp (normalClosure_normal.conj_mem g (le_normalClosure hg) h)

-- Wielandt claims that this is proved by the same method as above.
proof_wanted IsPreprimitive.is_two_pretransitive'
    (hG : IsPreprimitive G α)
    {s : Set α} {n : ℕ} (hsn : Nat.card s = n + 1) (hsn' : n + 1 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive (Subgroup.normalClosure (fixingSubgroup G s : Set G)) α 2

open MulAction.IsPreprimitive

open scoped Pointwise

/-- Simultaneously prove `MulAction.IsPreprimitive.is_two_pretransitive`
and `MulAction.IsPreprimitive.is_two_preprimitive`. -/
theorem MulAction.IsPreprimitive.is_two_motive_of_is_motive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α) :
    (IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)
      → IsMultiplyPretransitive G α 2)
    ∧ (IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)
      → IsMultiplyPreprimitive G α 2) := by
  induction n using Nat.strong_induction_on generalizing α G with
  | h n hrec =>
  have : Finite α := Nat.finite_of_card_ne_zero <| ne_zero_of_lt hsn'
  have hs_ne_univ : s ≠ Set.univ := by
    intro hs
    rw [hs, Set.ncard_univ] at hsn
    simp only [hsn, add_lt_add_iff_left, Nat.not_ofNat_lt_one] at hsn'
  have hs_nonempty : s.Nonempty := by
    simp [← Set.ncard_pos s.toFinite, hsn]
  -- The result is assumed by induction for sets of ncard ≤ n
  rcases Nat.lt_or_ge (n + 1) 2 with hn | hn
  · -- When n + 1 < 2 (imposes n = 0)
    have hn : n = 0 := by
      rwa [Nat.succ_lt_succ_iff, Nat.lt_one_iff] at hn
    simp only [hn, zero_add, Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    suffices IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) →
      IsMultiplyPretransitive G α 2 by
      refine ⟨this, fun hs_prim ↦ ?_⟩
      rw [hsa] at hs_prim
      rw [isMultiplyPreprimitive_succ_iff_ofStabilizer G α le_rfl (a := a),
        is_one_preprimitive_iff]
      exact IsPreprimitive.of_surjective
          ofFixingSubgroup_of_singleton_bijective.surjective
    rw [hsa]
    rw [ofStabilizer.isMultiplyPretransitive (a := a)]
    rw [is_one_pretransitive_iff]
    exact IsPretransitive.of_surjective_map
      ofFixingSubgroup_of_singleton_bijective.surjective
  rcases Nat.lt_or_ge (2 * (n + 1)) (Nat.card α) with hn1 | hn2
  · -- CASE where 2 * s.ncard < Nat.card α
    -- get a, b ∈ s, a ≠ b
    have : 1 < s.ncard := by rwa [hsn]
    rw [Set.one_lt_ncard] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    -- apply Rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ :=
      exists_mem_smul_and_notMem_smul (G := G) s.toFinite hs_nonempty hs_ne_univ hab
    let t := s ∩ g • s
    have ht : t.Finite := s.toFinite.inter_of_left (g • s)
    have htm : t.ncard = t.ncard - 1 + 1 := by
      apply (Nat.sub_eq_iff_eq_add ?_).mp rfl
      rw [Nat.one_le_iff_ne_zero]
      apply Set.ncard_ne_zero_of_mem (a := a) _ ht
      exact ⟨ha, hga⟩
    have hmn : t.ncard - 1 < n := by
      rw [Nat.lt_iff_add_one_le, ← htm, Nat.le_iff_lt_add_one, ← hsn]
      apply Set.ncard_lt_ncard _ s.toFinite
      exact ⟨Set.inter_subset_left, fun h ↦ hgb (Set.inter_subset_right (h hb))⟩
    have htm' : t.ncard - 1 + 2 < Nat.card α := lt_trans (Nat.add_lt_add_right hmn 2) hsn'
    suffices IsPretransitive ↥(fixingSubgroup G s) ↥(ofFixingSubgroup G s) →
      IsMultiplyPretransitive G α 2 by
      refine ⟨this, fun hs_prim ↦ ?_⟩
      have ht_prim : IsPreprimitive (fixingSubgroup G t) (ofFixingSubgroup G t) := by
        apply IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter hs_prim
        apply Set.union_ne_univ_of_ncard_add_ncard_lt
        rwa [Set.ncard_smul_set, hsn, ← two_mul]
      apply (hrec (t.ncard - 1) hmn hG htm htm').2 ht_prim
    intro hs_trans
    have ht_trans : IsPretransitive (fixingSubgroup G t) (ofFixingSubgroup G t) :=
      IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs_trans (by
        apply Set.union_ne_univ_of_ncard_add_ncard_lt
        rwa [Set.ncard_smul_set, hsn, ← two_mul])
    apply (hrec (t.ncard - 1) hmn hG htm ?_).1 ht_trans
    apply lt_trans _ hsn'
    exact Nat.add_lt_add_right hmn 2
  · -- CASE : 2 * s.ncard ≥ Nat.card α
    have : Set.Nontrivial sᶜ := by
      rwa [← Set.one_lt_encard_iff_nontrivial, ← sᶜ.toFinite.cast_ncard_eq, Nat.one_lt_cast,
        ← Nat.add_lt_add_iff_left, Set.ncard_add_ncard_compl, add_comm, hsn, add_comm]
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨a, ha : a ∈ sᶜ, b, hb : b ∈ sᶜ, hab⟩ := this
    -- apply Rudio to get g ∈ G such that a ∈ g • sᶜ, b ∉ g • sᶜ
    obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_notMem_smul (G := G)
      sᶜ.toFinite (Set.nonempty_of_mem ha)
      (by simpa [Set.nonempty_iff_ne_empty] using hs_nonempty)
      hab
    let t := s ∩ g • s
    have ha : a ∉ s ∪ g • s := by
      simp only [Set.smul_set_compl, Set.mem_compl_iff] at hga ha
      simp [ha, hga]
    have htm : t.ncard = t.ncard - 1 + 1 := by
      apply (Nat.sub_eq_iff_eq_add ?_).mp rfl
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Set.ncard_pos]
      apply Set.nonempty_inter_of_le_ncard_add_ncard
      · rw [Set.ncard_smul_set, ← two_mul, hsn]; exact hn2
      · exact fun h ↦ ha (by rw [h]; trivial)
    have hmn : t.ncard - 1 < n := by
      rw [Nat.lt_iff_add_one_le, ← htm, Nat.le_iff_lt_add_one, ← hsn]
      apply Set.ncard_lt_ncard _ (Set.toFinite s)
      refine ⟨Set.inter_subset_left, fun h ↦ hb ?_⟩
      suffices s = g • s by
        rw [this]
        simpa only [Set.smul_set_compl, Set.mem_compl_iff, Set.not_notMem] using hgb
      apply Set.eq_of_subset_of_ncard_le _ _ (g • s).toFinite
      · exact subset_trans h Set.inter_subset_right
      · rw [Set.ncard_smul_set]
    have htm' : t.ncard - 1 + 2 < Nat.card α := lt_trans (Nat.add_lt_add_right hmn 2) hsn'
    have hsgs_ne_top : s ∪ g • s ≠ ⊤ := fun h ↦ ha (h ▸ Set.mem_univ a)
    suffices IsPretransitive ↥(fixingSubgroup G s) ↥(ofFixingSubgroup G s) →
      IsMultiplyPretransitive G α 2 by
      refine ⟨this, fun hs_prim ↦ ?_⟩
      apply (hrec _ hmn hG htm htm').2
      exact IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
          hs_prim hsgs_ne_top
    intro hs_trans
    apply (hrec _ hmn hG htm htm').1
    exact IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs_trans hsgs_ne_top

/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
theorem MulAction.IsPreprimitive.is_two_pretransitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G α 2 :=
  (hG.is_two_motive_of_is_motive hsn hsn').1 hs_trans

/-- A criterion due to Jordan for being 2-preprimitive (Wielandt, 13.1) -/
theorem MulAction.IsPreprimitive.is_two_preprimitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α 2 :=
  (hG.is_two_motive_of_is_motive hsn hsn').2 hs_prim

-- Wielandt claims that this stronger version is proved in the same way
proof_wanted is_two_preprimitive_strong_jordan
    (hG : IsPreprimitive G α)
    {s : Set α} {n : ℕ} (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive (Subgroup.normalClosure (fixingSubgroup G s : Set G)) α 2

/-- Jordan's multiple primitivity criterion (Wielandt, 13.3) -/
theorem MulAction.IsPreprimitive.isMultiplyPreprimitive
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n + 1) (hsn' : n + 2 < Nat.card α)
    (hprim : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α (n + 2) := by
  have hα : Finite α := Or.resolve_right (finite_or_infinite α) (fun _ ↦ by
    simp [Nat.card_eq_zero_of_infinite] at hsn')
  induction n generalizing α hα G with
  | zero => -- case n = 0
    have : IsPretransitive G α := hG.toIsPretransitive
    simp only [zero_add, Set.ncard_eq_one] at hsn
    obtain ⟨a, rfl⟩ := hsn
    constructor
    · rw [ofStabilizer.isMultiplyPretransitive (a := a), is_one_pretransitive_iff]
      apply IsPretransitive.of_surjective_map
        ofFixingSubgroup_of_singleton_bijective.surjective hprim.toIsPretransitive
    · intro t h
      rw [zero_add, Nat.cast_ofNat, ← one_add_one_eq_two,
        (ENat.add_left_injective_of_ne_top ENat.one_ne_top).eq_iff] at h
      obtain ⟨b, htb⟩ := Set.encard_eq_one.mp h
      obtain ⟨g, hg⟩ := exists_smul_eq G a b
      have hst : g • ({a} : Set α) = ({b} : Set α) := by
        rw [Set.smul_set_singleton, hg]
      rw [htb]
      refine IsPreprimitive.of_surjective
        (conjMap_ofFixingSubgroup_bijective (hst := hst)).surjective
  -- Induction step
  | succ n hrec =>
    suffices ∃ (a : α) (t : Set (SubMulAction.ofStabilizer G a)),
      a ∈ s ∧ s = insert a (Subtype.val '' t) by
      obtain ⟨a, t, _, hst⟩ := this
      have ha' : a ∉ Subtype.val '' t := by
        intro h; rw [Set.mem_image] at h; obtain ⟨x, hx⟩ := h
        apply x.prop; rw [hx.right]; exact Set.mem_singleton a
      have ht_prim : IsPreprimitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
        rw [← is_one_preprimitive_iff]
        rw [← isMultiplyPreprimitive_succ_iff_ofStabilizer]
        · apply is_two_preprimitive hG hsn hsn' hprim
        · norm_num
      have : IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t)))
          (ofFixingSubgroup G (insert a (Subtype.val '' t))) :=
        IsPreprimitive.of_surjective
          (ofFixingSubgroup_of_eq_bijective (hst := hst)).surjective
      have hGs' : IsPreprimitive (fixingSubgroup (stabilizer G a) t)
        (ofFixingSubgroup (stabilizer G a) t) :=
        IsPreprimitive.of_surjective
          ofFixingSubgroup_insert_map_bijective.surjective
      rw [isMultiplyPreprimitive_succ_iff_ofStabilizer G (a := a) _ (Nat.le_add_left 1 (n + 1))]
      refine hrec ht_prim ?_ ?_ hGs' Subtype.finite
      · -- t.card = Nat.succ n
        rw [← Set.ncard_image_of_injective t Subtype.val_injective]
        apply Nat.add_right_cancel
        rw [← Set.ncard_insert_of_notMem ha', ← hst, hsn]
      · -- n + 2 < Nat.card (SubMulAction.ofStabilizer G α a)
        rw [← Nat.add_lt_add_iff_right, nat_card_ofStabilizer_add_one_eq]
        exact hsn'
    -- ∃ a t, a ∈ s ∧ s = insert a (Subtype.val '' t)
    suffices s.Nonempty by
      obtain ⟨a, ha⟩ := this
      use a, Subtype.val ⁻¹' s, ha
      ext x
      by_cases hx : x = a <;> simp [hx, mem_ofStabilizer_iff, ha]
    rw [← Set.ncard_pos, hsn]; apply Nat.succ_pos

end Jordan

section Subgroups

namespace Equiv.Perm

open Equiv Set

variable {α : Type*}

variable {G : Subgroup (Perm α)}

theorem subgroup_eq_top_of_nontrivial [Finite α] (hα : Nat.card α ≤ 2) (hG : Nontrivial G) :
    G = (⊤ : Subgroup (Perm α)) := by
  apply Subgroup.eq_top_of_le_card
  rw [Nat.card_perm]
  apply (Nat.factorial_le hα).trans
  rwa [Nat.factorial_two, Nat.succ_le, one_lt_card_iff_ne_bot, ← nontrivial_iff_ne_bot]

theorem isMultiplyPretransitive_of_nontrivial {K : Type*} [Group K] [MulAction K α]
    (hα : Nat.card α = 2) (hK : fixedPoints K α ≠ .univ) (n : ℕ) :
    IsMultiplyPretransitive K α n := by
  have : Finite α := Or.resolve_right (finite_or_infinite α) (fun _ ↦ by
    simp [Nat.card_eq_zero_of_infinite] at hα)
  have : Fintype α := Fintype.ofFinite α
  suffices h2 : IsMultiplyPretransitive K α 2 by
    by_cases hn : n ≤ 2
    · apply MulAction.isMultiplyPretransitive_of_le' hn
      simp [← hα]
    · suffices (IsEmpty (Fin n ↪ α)) by infer_instance
      rwa [← not_nonempty_iff, Function.Embedding.nonempty_iff_card_le, Fintype.card_fin,
        ← Nat.card_eq_fintype_card, hα]
  let φ := MulAction.toPermHom K α
  let f : α →ₑ[φ] α :=
    { toFun := id
      map_smul' := fun _ _ ↦ rfl }
  have hf : Function.Bijective f := Function.bijective_id
  suffices Function.Surjective φ by
    unfold IsMultiplyPretransitive
    rw [IsPretransitive.of_embedding_congr this hf (n := Fin 2), ← hα]
    apply Perm.isMultiplyPretransitive
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm (card_le_card_group φ.range)
  simp only [Nat.card_perm, hα, Nat.factorial_two]
  by_contra H
  simp only [not_le, Nat.lt_succ, Finite.card_le_one_iff_subsingleton] at H
  apply hK
  apply Set.eq_univ_of_univ_subset
  intro a _ g
  suffices φ g = φ 1 by
    conv_rhs => rw [← one_smul K a]
    simp only [← toPerm_apply, ← toPermHom_apply K α g]
    exact congrFun (congrArg DFunLike.coe this) a
  simpa [← Subtype.coe_inj] using H.elim ⟨_, ⟨g, rfl⟩⟩ ⟨_, ⟨1, rfl⟩⟩

variable [Fintype α] [DecidableEq α]

theorem isPretransitive_of_isCycle_mem {g : Perm α}
    (hgc : g.IsCycle) (hg : g ∈ G) :
    IsPretransitive (fixingSubgroup G (g.support : Set α)ᶜ)
      (SubMulAction.ofFixingSubgroup G (g.support : Set α)ᶜ) := by
  obtain ⟨a, _, hgc⟩ := hgc
  have hs : ∀ x : α, g • x ≠ x ↔
    x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    intro x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  suffices ∀ x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ),
      ∃ k : fixingSubgroup G ((↑g.support : Set α)ᶜ), x = k • a by
    rw [isPretransitive_iff]
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, hk⟩ := this x hx
    obtain ⟨k', hk'⟩ := this y hy
    use k' * k⁻¹
    rw [← SetLike.coe_eq_coe]
    simp only [SetLike.mk_smul_mk]
    rw [hk, hk', smul_smul, inv_mul_cancel_right]
  intro x hx
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    simp_rw [mem_fixingSubgroup_iff G]
    intro y hy
    simpa only [Set.mem_compl_iff, Finset.mem_coe, notMem_support] using hy
  let g' : fixingSubgroup (↥G) ((↑g.support : Set α)ᶜ) := ⟨(⟨g, hg⟩ : ↥G), hg'⟩
  obtain ⟨i, hi⟩ := hgc ((hs x).mpr hx)
  exact ⟨g' ^ i, hi.symm⟩

/-- A primitive subgroup of `Equiv.Perm α` that contains a swap
is the full permutation group (Jordan). -/
theorem eq_top_of_isPreprimitive_of_isSwap_mem
    (hG : IsPreprimitive G α) (g : Perm α) (h2g : IsSwap g) (hg : g ∈ G) :
    G = ⊤ := by
  classical
  rcases Nat.lt_or_ge (Nat.card α) 3 with hα3 | hα3
  · -- trivial case : Nat.card α ≤ 2
    rw [Nat.lt_succ_iff] at hα3
    apply Subgroup.eq_top_of_card_eq
    simp only [Nat.card_eq_fintype_card]
    apply le_antisymm (Fintype.card_subtype_le _)
    rw [← Nat.card_eq_fintype_card, Nat.card_perm]
    refine le_trans (Nat.factorial_le hα3) ?_
    rw [Nat.factorial_two]
    have : Nonempty G := One.instNonempty
    apply Nat.le_of_dvd Fintype.card_pos
    rw [← h2g.orderOf, orderOf_submonoid ⟨g, hg⟩]
    exact orderOf_dvd_card
  -- important case : Nat.card α ≥ 3
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hα3
  have hsc : Set.ncard ((g.support)ᶜ : Set α) = n + 1 := by
    apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset,
      card_support_eq_two.mpr h2g, add_comm, hn]
  apply eq_top_of_isMultiplyPretransitive
  suffices IsMultiplyPreprimitive G α (Nat.card α - 1) by
    apply IsMultiplyPreprimitive.isMultiplyPretransitive
  rw [show Nat.card α - 1 = n + 2 by grind]
  apply hG.isMultiplyPreprimitive hsc
  · rw [hn]; apply Nat.lt_add_one
  have := isPretransitive_of_isCycle_mem h2g.isCycle hg
  apply IsPreprimitive.of_prime_card
  convert Nat.prime_two
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_support_eq_two.mpr h2g]
  simp [SubMulAction.mem_ofFixingSubgroup_iff, support]

/-- A primitive subgroup of `Equiv.Perm α` that contains a 3-cycle
contains the alternating group (Jordan). -/
theorem alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    (hG : IsPreprimitive G α) {g : Perm α} (h3g : IsThreeCycle g) (hg : g ∈ G) :
    alternatingGroup α ≤ G := by
  classical
  rcases Nat.lt_or_ge (Nat.card α) 4 with hα4 | hα4
  · -- trivial case : Fintype.card α ≤ 3
    rw [Nat.lt_succ_iff] at hα4
    apply alternatingGroup_le_of_index_le_two
    rw [← Nat.mul_le_mul_right_iff (k:= Nat.card G) (Nat.card_pos),
      Subgroup.index_mul_card, Nat.card_perm]
    apply le_trans (Nat.factorial_le hα4)
    rw [show Nat.factorial 3 = 2 * 3 by simp [Nat.factorial]]
    simp only [mul_le_mul_iff_right₀, Nat.succ_pos]
    apply Nat.le_of_dvd Nat.card_pos
    suffices 3 = orderOf (⟨g, hg⟩ : G) by
      rw [this, Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    simp only [orderOf_mk, h3g.orderOf]
    -- important case : Nat.card α ≥ 4
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hα4
  apply IsMultiplyPretransitive.alternatingGroup_le
  suffices IsMultiplyPreprimitive G α (Nat.card α - 2) from
    IsMultiplyPreprimitive.isMultiplyPretransitive ..
  rw [show Nat.card α - 2 = n + 2 by grind]
  apply hG.isMultiplyPreprimitive (s := (g.supportᶜ : Set α))
  · apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset,
      h3g.card_support, add_comm, hn]
  · grind
  have := isPretransitive_of_isCycle_mem h3g.isCycle hg
  apply IsPreprimitive.of_prime_card
  convert Nat.prime_three
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← h3g.card_support]
  apply congr_arg
  ext x
  simp [SubMulAction.mem_ofFixingSubgroup_iff]

/-- A primitive subgroup of `Equiv.Perm α` that contains a cycle of prime order
contains the alternating group. -/
proof_wanted alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
  (hG : IsPreprimitive G α)
  {p : ℕ} (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α)
  {g : Perm α} (hgc : g.IsCycle) (hgp : g.support.card = p)
  (hg : g ∈ G) : alternatingGroup α ≤ G

end Equiv.Perm

end Subgroups
