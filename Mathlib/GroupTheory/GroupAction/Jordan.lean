/-
Copyright (c) 2025. Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.GroupAction.MultiplePrimitivity

/-! # Theorems of Jordan

A proof of theorems of Jordan regarding primitive permutation groups

This mostly follows the book of Wielandt, *Finite permutation groups*

- `is_two_pretransitive_weak_jordan` and `is_two_preprimitive_weak_jordan`
are technical lemmas that prove 2-pretransitivity / 2-preprimitivity
for some group actions (Wielandt, 13.1)

- `is_multiply_preprimitive_jordan` is a multiple preprimitivity criterion of Jordan (1871)
for a preprimitive action: the hypothesis is the preprimitivity
of the sub_mul_action of `fixing_subgroup s` (Wielandt, 13.2)

- `jordan_swap` proves that a primitive subgroup of a permutation group that contains a
swapis equal to the full permutation group (Wielandt, 13.3)

- `jordan_three_cycle` proves that a primitive subgroup of a permutation group that contains a
3-cycle contains the alternating group (Wielandt, 13.3)

## TODO

- Prove `jordan_prime_cycle` that a primitive subgroup of a permutation group that contains
a cycle of prime order contains the alternating group (Wielandt, 13.9 )

- Prove the stronger versions of the technical lemmas of Jordan. (Wielandt, 13.1')

- Golf the proofs of the technical lemmas (prove them at the same time, or find
an adequate induction lemma)
-/


section PigeonHole

namespace Set

variable {α : Type*} {s t : Set α}

theorem ncard_pigeonhole [Finite α]
    (h : Nat.card α < s.ncard + t.ncard) : (s ∩ t).Nonempty := by
  rw [← compl_ne_univ]
  intro h'
  apply not_le.mpr h
  rw [← ncard_union_add_ncard_inter]
  apply Nat.le_of_add_le_add_right
  rw [add_assoc, ncard_add_ncard_compl, h', ncard_univ, add_le_add_iff_right, ← ncard_univ]
  apply ncard_le_ncard (subset_univ _)

theorem ncard_lt (h : s.ncard < Nat.card α) : s ≠ ⊤ := fun h' ↦ by
  apply not_le.mpr h
  rw [h', top_eq_univ, ncard_univ]

theorem ncard_pigeonhole' [Finite α]
    (h' : Nat.card α ≤ s.ncard + t.ncard) (h : s ∪ t ≠ ⊤) :
    (s ∩ t).Nonempty := by
  rw [← ncard_pos]
  apply Nat.lt_of_add_lt_add_right
  rw [ncard_inter_add_ncard_union, zero_add]
  apply lt_of_lt_of_le _ h'
  rw [← not_le]
  intro H
  apply h
  rw [top_eq_univ, eq_univ_iff_ncard]
  apply le_antisymm _ H
  rw [← ncard_univ]
  exact ncard_le_ncard (subset_univ _)

theorem ncard_pigeonhole_compl
    (h : s.ncard + t.ncard < Nat.card α) : (sᶜ ∩ tᶜ).Nonempty := by
  have : Finite α := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt h)
  simp only [← compl_ne_univ, compl_inter, compl_compl]
  intro H
  apply not_le.mpr h
  rw [← ncard_inter_add_ncard_union, H, ncard_univ]
  exact Nat.le_add_left (Nat.card α) (s ∩ t).ncard

  theorem ncard_pigeonhole_compl'
    (h : s.ncard + t.ncard < Nat.card α) : s ∪ t ≠ ⊤ := by
  intro h'
  apply not_le.mpr h
  rw [← ncard_univ, ← top_eq_univ, ← h']
  exact ncard_union_le s t

end Set

end PigeonHole

open MulAction SubMulAction Subgroup

open scoped Pointwise

/-- A pretransitivity criterion -/
theorem IsPretransitive.isPretransitive_ofFixingSubgroup_inter
    {α : Type*} {G : Type*} [Group G] [MulAction G α] {s : Set α}
    (hs : IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s))
    {g : G} (ha : s ∪ g • s ≠ ⊤) :
    IsPretransitive (fixingSubgroup G (s ∩ g • s)) (ofFixingSubgroup G (s ∩ g • s)) := by
  rw [Ne, Set.top_eq_univ, ← Set.compl_empty_iff, ← Ne, ← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  have ha' : a ∈ (s ∩ g • s)ᶜ := by
    rw [Set.compl_inter]
    apply Set.mem_union_left
    rw [Set.compl_union] at ha
    apply Set.mem_of_mem_inter_left ha
  rw [isPretransitive_iff_base (⟨a, ha'⟩ : ofFixingSubgroup G (s ∩ g • s))]
  rintro ⟨x, hx⟩
  rw [mem_ofFixingSubgroup_iff, Set.mem_inter_iff, not_and_or] at hx
  rcases hx with hx | hx
  · obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq
      ⟨a, (by intro ha'; apply ha; apply Set.mem_union_left _ ha')⟩
      ⟨x, hx⟩
    use ⟨k, (by
      rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y  hy
      apply hk
      apply Set.mem_of_mem_inter_left hy)⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      exact hkax
  · suffices hg'x : g⁻¹ • x ∈ ofFixingSubgroup G s by
      suffices hg'a : g⁻¹ • a ∈ ofFixingSubgroup G s by
        obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq ⟨g⁻¹ • a, hg'a⟩ ⟨g⁻¹ • x, hg'x⟩
        use ⟨g * k * g⁻¹, (by
          rw [mem_fixingSubgroup_iff] at hk ⊢
          intro y hy
          simp [← smul_smul, smul_eq_iff_eq_inv_smul g]
          apply hk
          rw [← Set.mem_smul_set_iff_inv_smul_mem]
          exact Set.mem_of_mem_inter_right hy)⟩
        · simp only [← SetLike.coe_eq_coe] at hkax ⊢
          simp only [SetLike.val_smul] at hkax ⊢
          rw [← smul_eq_iff_eq_inv_smul] at hkax
          change (g * k * g⁻¹) • a = x
          simp only [← smul_smul]
          exact hkax
      rw [mem_ofFixingSubgroup_iff]
      rw [← Set.mem_smul_set_iff_inv_smul_mem]
      intro h
      apply ha
      apply Set.mem_union_right _ h
    rw [mem_ofFixingSubgroup_iff]
    intro h
    apply hx
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact h

lemma _root_.SubMulAction.add_encard_ofStabilizer_eq
    (G : Type*) {α : Type*} [Group G] [MulAction G α] (a : α) :
    1 + (ofStabilizer G a).carrier.encard = ENat.card α :=  by
  classical
  rw [ofStabilizer_carrier]
  convert Set.encard_add_encard_compl {a}
  · rw [Set.encard_singleton]
  · exact (Set.encard_univ α).symm

/- lemma _root_.SubMulAction.add_encard_ofStabilizer_eq'
    (G : Type*) {α : Type*} [Group G] [MulAction G α] (a : α) :
    1 + (SubMulAction.ofStabilizer G a).carrier.encard =
      Set.encard (Set.univ : Set α) :=  by
  rw [SubMulAction.add_encard_ofStabilizer_eq, Set.encard_univ] -/

section Jordan


variable {G α : Type*} [Group G] [MulAction G α]

/-- In a 2-pretransitive action, the normal closure of stabilizers is the full group -/
theorem normalClosure_of_stabilizer_eq_top (hsn' : 2 < ENat.card α)
    (hG' : IsMultiplyPretransitive G α 2) {a : α} :
    normalClosure ((stabilizer G a) : Set G) = ⊤ := by
  have hG : IsPretransitive G α := by
    rw [← is_one_pretransitive_iff]
    exact isMultiplyPretransitive_of_le' (one_le_two) (le_of_lt hsn')
  have : Nontrivial α := by
    rw [← ENat.one_lt_card_iff_nontrivial]
    exact lt_trans (by norm_num) hsn'
  have hGa : IsCoatom (stabilizer G a) :=  by
    rw [isCoatom_stabilizer_iff_preprimitive]
    exact isPreprimitive_of_is_two_pretransitive hG'
  apply hGa.right
  -- Remains to prove: (stabilizer G a) < Subgroup.normalClosure (stabilizer G a)
  constructor
  · apply le_normalClosure
  · intro hyp
    have : Nontrivial (ofStabilizer G a) := by
      apply Set.Nontrivial.coe_sort
      rw [← Set.one_lt_encard_iff_nontrivial]
      rw [← not_le]
      rw [← AddLECancellable.add_le_add_iff_left (ENat.addLECancellable_of_ne_top ENat.one_ne_top)]
      simp only [SetLike.coe, add_encard_ofStabilizer_eq G a]
      rwa [not_le]
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

variable [Finite α]

/-- A primitivity criterion -/
theorem IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
    {G : Type*} [Group G] [MulAction G α] {s : Set α}
    (hs : IsPreprimitive (fixingSubgroup G s) (ofFixingSubgroup G s))
    {g : G} (ha : s ∪ g • s ≠ ⊤) :
    IsPreprimitive (fixingSubgroup G (s ∩ g • s)) (ofFixingSubgroup G (s ∩ g • s)) := by
  classical
  have hts : s ∩ g • s ≤ s := Set.inter_subset_left
  --  IsPretransitive (fixingSubgroup G (s ∩ g • s)) (ofFixingSubgroup G (s ∩ g • s)) :=
  have := IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha

  apply IsPreprimitive.of_card_lt (f := ofFixingSubgroup_of_inclusion G hts)

  rw [← Set.image_univ,
    Set.ncard_image_of_injective _ (ofFixingSubgroup_of_inclusion_injective G _)]

  have this : Set.ncard (s ∩  g • s)ᶜ < 2 * Set.ncard (sᶜ) := by
    rw [Set.compl_inter, ← Nat.add_lt_add_iff_right, Set.ncard_union_add_ncard_inter]
    rw [← Set.compl_union, two_mul, add_assoc]
    simp only [add_lt_add_iff_left]
    rw [← add_lt_add_iff_left, Set.ncard_add_ncard_compl,
      Set.ncard_smul_set, ← add_assoc, Set.ncard_add_ncard_compl]
    simp only [lt_add_iff_pos_right]
    rwa [Set.ncard_pos, Set.nonempty_compl]
  convert this
  rw [← ofFixingSubgroup_carrier G,
    ← Set.ncard_image_of_injective (Set.univ) (ofFixingSubgroup G s).inclusion_injective,
    ← image_inclusion, Set.image_univ]

-- α = Ω, s = Δ, α \ s = Γ
-- 1 ≤ #Δ < #Ω, 1 < #Γ < #Ω
/- -- TODO : prove :
theorem strong_jordan_of_pretransitive (hG : is_preprimitive G α)
    {s : set α} {n : ℕ } (hsn : fintype.card s = n.succ)
    (hsn' : 1 + n.succ < fintype.card α)
    (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 :=
sorry
 -/

open MulAction.IsPreprimitive

open scoped Pointwise

/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
theorem is_two_pretransitive_weak_jordan [DecidableEq α]
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n.succ) (hsn' : 1 + n.succ < Nat.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G α 2 := by
  revert α G
  induction' n using Nat.strong_induction_on with n hrec
  intro G α _ _ _ _ hG s hsn hsn' hs_trans

  have hs_ne_top : s ≠ ⊤ := by
    intro hs
    rw [hs, Set.top_eq_univ, Set.ncard_univ] at hsn
    rw [← hsn, add_lt_iff_neg_right] at hsn'
    contradiction

  have hs_nonempty : s.Nonempty := by
    rw [← Set.ncard_pos, hsn]
    exact Nat.succ_pos n

  rcases Nat.lt_or_ge n.succ 2 with hn | hn

  · -- Initialization : n = 0
    have hn : n = 0 := by
      rw [← le_zero_iff]
      apply Nat.le_of_succ_le_succ
      apply Nat.le_of_lt_succ
      exact hn

    simp only [hn, Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    rw [hsa] at hs_trans

    rw [ofStabilizer.isMultiplyPretransitive (a := a)]
    rw [is_one_pretransitive_iff]

    apply IsPretransitive.of_surjective_map
      (ofFixingSubgroup_of_singleton_bijective G a).surjective hs_trans

  -- The result is assumed by induction for sets of ncard ≤ n

  rcases Nat.lt_or_ge (2 * n.succ) (Nat.card α) with hn1 | hn2

  · -- CASE where 2 * s.ncard < fintype.card α
    -- get a, b ∈ s, a ≠ b
    have : 1 < s.ncard := by rw [hsn]; exact hn
    rw [Set.one_lt_ncard] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    -- apply Rudio's theorem to get g ∈ G such that a ∈ g • s, b ∉ g • s
    classical
    obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_not_mem_smul (G := G)
      s.toFinite hs_nonempty hs_ne_top hab

    let t := s ∩ g • s
    have ht_trans : IsPretransitive (fixingSubgroup G t) (ofFixingSubgroup G t) :=
      IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs_trans (by
        apply Set.ncard_pigeonhole_compl'
        rw [Set.ncard_smul_set, hsn, ← two_mul]
        exact hn1)
    suffices ∃ m, m < n ∧ t.ncard = Nat.succ m by
      obtain ⟨m, hmn, htm⟩ := this
      apply hrec m hmn hG htm _ ht_trans
      apply lt_trans _ hsn'
      rw [add_lt_add_iff_left, Nat.succ_lt_succ_iff]
      exact hmn
    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- deduce : 1 ≤ t.ncard < s.ncard
    use t.ncard.pred
    suffices t.ncard ≠ 0 by
      rw [← Nat.succ_lt_succ_iff, ← hsn, Nat.succ_pred this]
      refine ⟨?_, rfl⟩
      apply Set.ncard_lt_ncard _ (Set.toFinite s)
      exact ⟨Set.inter_subset_left, fun h ↦ hgb (Set.inter_subset_right (h hb))⟩
    apply Set.ncard_ne_zero_of_mem (a := a)
    exact ⟨ha, hga⟩


  · -- CASE : 2 * s.ncard ≥ Nat.card α
    have : Set.Nontrivial sᶜ := by
      rw [← Set.one_lt_encard_iff_nontrivial, ← sᶜ.toFinite.cast_ncard_eq, Nat.one_lt_cast]
      rw [← Nat.add_lt_add_iff_left, Set.ncard_add_ncard_compl, add_comm, hsn]
      exact hsn'
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨a, ha : a ∈ sᶜ, b, hb : b ∈ sᶜ, hab⟩ := this

    obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_not_mem_smul (G := G)
      sᶜ.toFinite (Set.nonempty_of_mem ha)
      (by intro h
          simp only [Set.top_eq_univ, Set.compl_univ_iff] at h
          simp only [h, Set.not_nonempty_empty] at hs_nonempty)
      hab
    let t := s ∩ g • s
    have : a ∉ s ∪ g • s := by
      rw [Set.mem_union]
      intro h
      rcases h with h | h
      · exact ha h
      · rw [Set.smul_set_compl] at hga; exact hga h
    have ht_trans : IsPretransitive (fixingSubgroup G t) (ofFixingSubgroup G t) :=
        IsPretransitive.isPretransitive_ofFixingSubgroup_inter hs_trans
          (fun h ↦ this (by rw [h]; trivial))

    suffices ∃ m : ℕ, m < n ∧ t.ncard = Nat.succ m by
      obtain ⟨m, hmn, htm⟩ := this
      refine hrec m hmn hG htm (by
        apply lt_trans _ hsn'
        rw [add_lt_add_iff_left, Nat.succ_lt_succ_iff]
        exact hmn) ht_trans

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ t.ncard < fintype.card s
    use t.ncard.pred
    suffices  t.ncard ≠ 0 by
      rw [← Nat.succ_lt_succ_iff, ← hsn, Nat.succ_pred this]
      refine ⟨?_, rfl⟩
      apply Set.ncard_lt_ncard _ (Set.toFinite s)
      rw [Set.ssubset_def]
      refine ⟨Set.inter_subset_left, fun h ↦ hb ?_⟩
      suffices s = g • s by
        rw [this]
        simpa only [Set.smul_set_compl, Set.mem_compl_iff, Set.not_not_mem] using hgb
      apply Set.eq_of_subset_of_ncard_le _ _ (g • s).toFinite
      · exact subset_trans h Set.inter_subset_right
      · rw [Set.ncard_smul_set]
    · rw [← Nat.pos_iff_ne_zero, Set.ncard_pos]
      -- variante de Set.ncard_pigeonhole qui utilise que la réunion n'est pas top
      simp only [t]
      apply Set.ncard_pigeonhole'
      · rw [Set.ncard_smul_set, ← two_mul, hsn]; exact hn2
      · exact fun h ↦ this (by rw [h]; trivial)

/- -- TODO : prove
theorem strong_jordan_of_preprimitive (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_preprimitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 := sorry
 -/

theorem is_two_preprimitive_weak_jordan [DecidableEq α]
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n.succ) (hsn' : 1 + n.succ < Nat.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α 2 := by
  revert α G
  induction' n using Nat.strong_induction_on with n hrec
  intro G α _ _ _ _ hG s hsn hsn' hs_prim

  have hs_ne_top : s ≠ ⊤ := by
    intro hs
    rw [hs, Set.top_eq_univ, Set.ncard_univ] at hsn
    rw [← hsn, add_lt_iff_neg_right] at hsn'
    contradiction

  have hs_nonempty : s.Nonempty := by
    rw [← Set.ncard_pos, hsn]
    exact Nat.succ_pos n

  -- The result is assumed by induction for sets of ncard ≤ n

  rcases Nat.lt_or_ge n.succ 2 with hn | hn

  · -- When n < 2 (imposes n = 0)
    have hn : n = 0 := by
      rw [← le_zero_iff]
      apply Nat.le_of_succ_le_succ
      apply Nat.le_of_lt_succ
      exact hn

    simp only [hn, Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    rw [hsa] at hs_prim

    rw [isMultiplyPreprimitive_succ_iff_ofStabilizer (M := G) (a := a)]
    · rw [is_one_preprimitive_iff (stabilizer G a) (ofStabilizer G a)]
      exact IsPreprimitive.of_surjective
        (ofFixingSubgroup_of_singleton_bijective G a).surjective
    · norm_num

  rcases Nat.lt_or_ge (2 * n.succ) (Nat.card α) with hn1 | hn2

  · -- CASE where 2 * s.ncard < fintype.card α
    -- get a, b ∈ s, a ≠ b
    have : 1 < s.ncard := by rw [hsn]; exact hn
    rw [Set.one_lt_ncard] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_not_mem_smul (G := G)
      s.toFinite hs_nonempty hs_ne_top hab

    let t := s ∩ g • s
    have ht_prim : IsPreprimitive (fixingSubgroup G t) (ofFixingSubgroup G t) := by
      apply IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter hs_prim
      apply Set.ncard_pigeonhole_compl'
      rw [Set.ncard_smul_set, hsn, ← two_mul]
      exact hn1
    suffices ∃ m, m < n ∧ t.ncard = Nat.succ m by
      obtain ⟨m, hmn, htm⟩ := this
      apply hrec m hmn hG htm _ ht_prim
      · apply lt_trans _ hsn'
        rw [add_lt_add_iff_left, Nat.succ_lt_succ_iff]
        exact hmn

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- deduce : 1 ≤ t.ncard < s.ncard
    use t.ncard.pred
    suffices t.ncard ≠ 0 by
      rw [← Nat.succ_lt_succ_iff, ← hsn, Nat.succ_pred this]
      constructor
      · apply Set.ncard_lt_ncard _ (Set.toFinite s)
        constructor
        apply Set.inter_subset_left
        intro h
        apply hgb
        apply Set.inter_subset_right
        apply h
        exact hb
      · rfl
    · apply Set.ncard_ne_zero_of_mem (a := a)
      exact ⟨ha, hga⟩

  · -- CASE : 2 * s.ncard ≥ Fintype.card α
    have : Set.Nontrivial sᶜ := by
      rw [← Set.one_lt_encard_iff_nontrivial, ← sᶜ.toFinite.cast_ncard_eq, Nat.one_lt_cast,
        ← Nat.add_lt_add_iff_left, Set.ncard_add_ncard_compl, add_comm, hsn]
      exact hsn'
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨a, ha : a ∈ sᶜ, b, hb : b ∈ sᶜ, hab⟩ := this

    obtain ⟨g, hga, hgb⟩ := exists_mem_smul_and_not_mem_smul (G := G)
      sᶜ.toFinite (Set.nonempty_of_mem ha)
      (by intro h
          simp only [Set.top_eq_univ, Set.compl_univ_iff] at h
          simp only [h, Set.not_nonempty_empty] at hs_nonempty)
      hab
    let t := s ∩ g • s
    have : a ∉ s ∪ g • s := by
      rw [Set.mem_union]
      intro h
      rcases h with h | h
      · exact ha h
      · rw [Set.smul_set_compl] at hga; exact hga h
    have ht_prim : IsPreprimitive (fixingSubgroup G t) (ofFixingSubgroup G t) :=
        IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter hs_prim
        (by intro h; apply this; rw [h]; trivial)

    suffices ∃ m : ℕ, m < n ∧ t.ncard = Nat.succ m by
      obtain ⟨m, hmn, htm⟩ := this
      exact hrec m hmn hG htm (by
        apply lt_trans _ hsn'
        rw [add_lt_add_iff_left, Nat.succ_lt_succ_iff]
        exact hmn) ht_prim

    -- from : t ⊆ s, a ∈ t, b ∉ t,
    -- have : 1 ≤ t.ncard < fintype.card s
    use t.ncard.pred
    suffices  t.ncard ≠ 0 by
      rw [← Nat.succ_lt_succ_iff, ← hsn, Nat.succ_pred this]
      refine ⟨?_, rfl⟩
      apply Set.ncard_lt_ncard _ (Set.toFinite s)
      rw [Set.ssubset_def]
      refine ⟨Set.inter_subset_left, fun h ↦ hb ?_⟩
      suffices s = g • s by
        rw [this]
        simpa only [Set.smul_set_compl, Set.mem_compl_iff, Set.not_not_mem] using hgb
      apply Set.eq_of_subset_of_ncard_le _ _ (g • s).toFinite
      · exact subset_trans h Set.inter_subset_right
      · rw [Set.ncard_smul_set]
    · rw [← Nat.pos_iff_ne_zero]
      -- variante de Set.ncard_pigeonhole qui utilise que la réunion n'est pas top
      apply Nat.lt_of_add_lt_add_right
      rw [Set.ncard_inter_add_ncard_union, zero_add, Set.ncard_smul_set, hsn, ← two_mul]
      apply lt_of_lt_of_le _ hn2
      rw [← not_le]
      intro h
      apply this
      convert Set.mem_univ a
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ Set.finite_univ
      simpa only [Set.ncard_univ]

/- These theorems will be deduced from the strong one
theorem is_two_pretransitive_weak_jordan' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_trans : is_pretransitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_pretransitive G α 2 :=
begin
 -- We can deduce it from jordan0
  apply is_pretransitive_of_subgroup,
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply strong_jordan_of_pretransitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_trans,
end

theorem weak_jordan_of_preprimitive' (hG : is_preprimitive G α)
  {s : set α} (hs : 1 ≤ fintype.card s) (hs' : 2 + fintype.card (s) ≤ fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action_of_fixing_subgroup G s)) :
  is_multiply_preprimitive G α 2 :=
begin
 -- We can deduce it from strong_jordan_of_preprimitive
  obtain ⟨n,hn : fintype.card ↥s = n.succ⟩ := nat.exists_eq_succ_of_ne_zero
    (nat.one_le_iff_ne_zero.mp hs),
  apply is_multiply_preprimitive_of_subgroup,
  norm_num,
  refine strong_jordan_of_preprimitive hG hn
    (begin rw hn at hs', apply lt_of_lt_of_le _ hs', norm_num,  end)
    hs_prim
end
-/

-- Notations of Wielandt : s = Δ, n - m = #s, n = #α, m = #sᶜ, 1 < m < n
-- 1 + #s < n , #s ≥ 1
/-- Jordan's multiple primitivity criterion (Wielandt, 13.3) -/
theorem isMultiplyPreprimitive_jordan
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n.succ) (hsn' : 1 + n.succ < Nat.card α)
    (hprim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α (1 + n.succ) := by
  classical
  revert α G
  induction' n with n hrec

  · -- case n = 0
    intro G α _ _ _ hG s hsn _ hGs
    haveI : IsPretransitive G α := hG.toIsPretransitive
    simp only [Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    rw [hsa] at hGs

    constructor
    · rw [ofStabilizer.isMultiplyPretransitive (a := a)]
      rw [is_one_pretransitive_iff]
      apply IsPretransitive.of_surjective_map
        (ofFixingSubgroup_of_singleton_bijective G a).surjective hGs.toIsPretransitive
    · intro t h
      simp only [Nat.cast_add, Nat.cast_one,
        (ENat.add_left_injective_of_ne_top ENat.one_ne_top).eq_iff] at h

      obtain ⟨b, htb⟩ := Set.encard_eq_one.mp h
      obtain ⟨g, hg⟩ := exists_smul_eq G a b
      have hst : g • ({a} : Set α) = ({b} : Set α) := by
        change (fun x => g • x) '' {a} = {b}
        rw [Set.image_singleton, hg]
      rw [htb]
      refine IsPreprimitive.of_surjective
        (conjMap_ofFixingSubgroup_bijective _ _ hst).surjective

  -- Induction step
  intro G α _ _ _ hG s hsn hα hGs
  suffices ∃ (a : α) (t : Set (SubMulAction.ofStabilizer G a)),
    a ∈ s ∧ s = insert a (Subtype.val '' t) by
    obtain ⟨a, t, _, hst⟩ := this
    have ha' : a ∉ Subtype.val '' t := by
      intro h; rw [Set.mem_image] at h ; obtain ⟨x, hx⟩ := h
      apply x.prop; rw [hx.right]; exact Set.mem_singleton a
    have ht_prim : IsPreprimitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
      rw [← is_one_preprimitive_iff]
      rw [← isMultiplyPreprimitive_succ_iff_ofStabilizer]
      apply is_two_preprimitive_weak_jordan hG hsn hα hGs
      norm_num

    have : IsPreprimitive ↥(fixingSubgroup G (insert a (Subtype.val '' t)))
        (ofFixingSubgroup G (insert a (Subtype.val '' t))) :=
      IsPreprimitive.of_surjective
        (ofFixingSubgroup_of_eq_bijective G hst).surjective
    have hGs' : IsPreprimitive (fixingSubgroup (stabilizer G a) t)
      (ofFixingSubgroup (stabilizer G a) t) :=
      IsPreprimitive.of_surjective
        (ofFixingSubgroup_insert_map_bijective G a t).surjective
    rw [← Nat.succ_eq_one_add]
    rw [isMultiplyPreprimitive_succ_iff_ofStabilizer (M := G) (a := a)]
    -- stabilizer.isMultiplyPreprimitive G α _ hG.toIsPretransitive]
    suffices n + 2 = 1 + Nat.succ n by
      rw [this]
      refine hrec ht_prim ?_ ?_ hGs'
      · -- t.card = Nat.succ n
        rw [← Set.ncard_image_of_injective t Subtype.val_injective]
        apply Nat.add_right_cancel
        rw [← Set.ncard_insert_of_not_mem ha', ← hst, hsn]
      · -- 1 + n.succ < Fintype.card (SubMulAction.ofStabilizer G α a)
        change _ < Nat.card (ofStabilizer G a).carrier
        rw [Set.Nat.card_coe_set_eq, ofStabilizer_carrier, ← Nat.succ_eq_one_add]
        apply Nat.lt_of_add_lt_add_left
        rw [Set.ncard_add_ncard_compl]
        simpa only [Set.ncard_singleton]
    · exact Nat.succ_eq_one_add (n + 1)
    · exact Nat.le_add_left 1 (n + 1)
  -- ∃ a t, a ∈ s ∧ s = insert a (Subtype.val '' t)
  suffices s.Nonempty by
    obtain ⟨a, ha⟩ := this
    use a, Subtype.val ⁻¹' s, ha
    ext x
    suffices x ∈ s ↔ x = a ∨ x ∈ s ∧ ¬x = a by
      simpa [mem_ofStabilizer_iff]
    by_cases hx : x = a <;> simp [hx, ha]
  rw [← Set.ncard_pos, hsn]; apply Nat.succ_pos

end Jordan

