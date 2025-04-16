/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

-- import Jordan.Mathlib.Set
-- import Jordan.Primitive
-- import Jordan.IndexNormal
-- import Jordan.MultiplePrimitivity
--
import Mathlib.GroupTheory.GroupAction.MultiplePrimitivity
import Mathlib.GroupTheory.Perm.Support
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Set.Card

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
swap is equal to the full permutation group (Wielandt, 13.3)

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

open scoped Set BigOperators Pointwise Classical

variable {α : Type*} [Fintype α]

theorem Set.ncard_pigeonhole {s t : Set α}
    (h : Fintype.card α < s.ncard + t.ncard) :
    (s ∩ t).Nonempty := by
  rw [← compl_ne_univ]
  intro h'
  apply not_le.mpr h
  rw [← Set.ncard_union_add_ncard_inter]
  apply Nat.le_of_add_le_add_right
  rw [add_assoc, Set.ncard_add_ncard_compl, h', Set.ncard_univ, ← Nat.card_eq_fintype_card, add_le_add_iff_right, ← Set.ncard_univ]
  apply Set.ncard_le_ncard (subset_univ _)

theorem Set.ncard_pigeonhole_compl {s t : Set α}
    (h : s.ncard + t.ncard < Fintype.card α) :
    (sᶜ ∩ tᶜ).Nonempty := by
  apply Set.ncard_pigeonhole
  apply Nat.lt_of_add_lt_add_left
  rw [← add_assoc, Set.ncard_add_ncard_compl]
  simp only [Nat.card_eq_fintype_card, add_comm, add_lt_add_iff_left]
  apply Nat.lt_of_add_lt_add_left
  rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, add_comm]
  exact h

theorem Set.ncard_pigeonhole_compl' {s t : Set α}
    (h : s.ncard + t.ncard < Fintype.card α) :
    s ∪ t ≠ ⊤ := by
  intro h'
  apply not_le.mpr h
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ, ← top_eq_univ, ← h']
  exact ncard_union_le s t

end PigeonHole

open MulAction

open scoped Pointwise

instance  {α : Type _} {G : Type _} [Group G] [MulAction G α] {s : Set α} :
    SMul (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) :=
  SetLike.smul (SubMulAction.ofFixingSubgroup G s)

/-- A pretransitivity criterion -/
theorem isPretransitive_ofFixingSubgroup_inter
    {α : Type _} {G : Type _} [Group G] [MulAction G α]
    {s : Set α} (hs : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s))
    {g : G} (ha : s ∪ g • s ≠ ⊤) :  -- {a : α} (ha : a ∉ s ∪ g • s) :
    IsPretransitive (fixingSubgroup G (s ∩ g • s)) (SubMulAction.ofFixingSubgroup G (s ∩ g • s)) := by
  rw [Ne, Set.top_eq_univ, ← Set.compl_empty_iff, ← Ne, ← Set.nonempty_iff_ne_empty] at ha
  obtain ⟨a, ha⟩ := ha
  have ha' : a ∈ (s ∩ g • s)ᶜ := by
    rw [Set.compl_inter]
    apply Set.mem_union_left
    rw [Set.compl_union] at ha
    apply Set.mem_of_mem_inter_left ha
  -- For an unknown reason, rw does not work
  apply (IsPretransitive.mk_base_iff (⟨a, ha'⟩ : SubMulAction.ofFixingSubgroup G (s ∩ g • s))).mpr
  -- let hs_trans_eq := hs.exists_smul_eq
  rintro ⟨x, hx⟩
  rw [SubMulAction.mem_ofFixingSubgroup_iff, Set.mem_inter_iff, not_and_or] at hx
  cases' hx with hx hx
  · -- x ∉ s
    obtain ⟨⟨k, hk⟩, hkax⟩ := hs.exists_smul_eq
      ⟨a, (by intro ha'; apply ha; apply Set.mem_union_left _ ha')⟩
      ⟨x, hx⟩
    use ⟨k, (by
      rw [mem_fixingSubgroup_iff] at hk ⊢
      intro y  hy
      apply hk
      apply Set.mem_of_mem_inter_left hy)⟩
    · simp only [← SetLike.coe_eq_coe] at hkax ⊢
      exact hkax
  · -- x ∉ g • s
    suffices hg'x : g⁻¹ • x ∈ SubMulAction.ofFixingSubgroup G s by
      suffices hg'a : g⁻¹ • a ∈ SubMulAction.ofFixingSubgroup G s by
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
      rw [SubMulAction.mem_ofFixingSubgroup_iff]
      rw [← Set.mem_smul_set_iff_inv_smul_mem]
      intro h
      apply ha
      apply Set.mem_union_right _ h
    rw [SubMulAction.mem_ofFixingSubgroup_iff]
    intro h
    apply hx
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    exact h

lemma _root_.SubMulAction.add_encard_ofStabilizer_eq
    {G : Type _} [Group G] [MulAction G α] (a : α) :
    1 + (SubMulAction.ofStabilizer G a).carrier.encard = ENat.card α :=  by
  classical
  rw [SubMulAction.ofStabilizer_carrier]
  convert Set.encard_add_encard_compl {a}
  · rw [Set.encard_singleton]
  · exact (Set.encard_univ α).symm

lemma _root_.SubMulAction.add_encard_ofStabilizer_eq'
    {G : Type _} [Group G] [MulAction G α] (a : α) :
    1 + (SubMulAction.ofStabilizer G a).carrier.encard =
      Set.encard (Set.univ : Set α) :=  by
  rw [SubMulAction.ofStabilizer_carrier]
  convert Set.encard_add_encard_compl _
  simp only [Set.encard_singleton]

section Jordan

variable {α : Type _}

variable {G : Type _} [Group G] [MulAction G α]

/-- In a 2-pretransitive action, the normal closure of stabilizers is the full group -/
theorem normalClosure_of_stabilizer_eq_top (hsn' : 2 < ENat.card α)
    (hG' : IsMultiplyPretransitive G α 2) {a : α} :
    Subgroup.normalClosure ((stabilizer G a) : Set G) = ⊤ := by
  have hG : IsPretransitive G α := by
    rw [isPretransitive_iff_is_one_pretransitive]
    apply isMultiplyPretransitive_of_higher
    exact hG'
    norm_num
    rw [Nat.cast_two]
    exact le_of_lt hsn'
  have : Nontrivial α := by
    rw [← ENat.one_lt_card_iff_nontrivial]
    refine lt_trans ?_ hsn'
    rw [← Nat.cast_two, ← Nat.cast_one, ENat.coe_lt_coe]
    norm_num
  have hGa : (stabilizer G a).IsMaximal :=  by
    rw [maximal_stabilizer_iff_preprimitive G a]
    exact hG'.isPreprimitive_of_two
  rw [Subgroup.isMaximal_def] at hGa
  apply hGa.right
  -- Remains to prove: (stabilizer G a) < Subgroup.normalClosure (stabilizer G a)
  constructor
  · apply Subgroup.le_normalClosure
  · intro hyp
    have : Nontrivial (SubMulAction.ofStabilizer G a) := by
      apply Set.Nontrivial.coe_sort
      rw [← Set.one_lt_encard_iff_nontrivial]
      rw [← not_le, ← Nat.cast_one, ← WithTop.add_one_le_coe_succ_iff, not_le]
      rw [← Set.encard_univ] at hsn'
      convert hsn'
      rw [add_comm]
      simpa using SubMulAction.add_encard_ofStabilizer_eq' a
    rw [nontrivial_iff] at this
    obtain ⟨b, c, hbc⟩ := this
    have : IsPretransitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
      rw [isPretransitive_iff_is_one_pretransitive]
      exact (stabilizer.isMultiplyPretransitive G α hG).mp hG'
    -- trouver g ∈ stabilizer G a, g • b = c,
    obtain ⟨⟨g, hg⟩, hgbc⟩ := exists_smul_eq (stabilizer G a) b c
    apply hbc
    rw [← SetLike.coe_eq_coe]
    rw [← SetLike.coe_eq_coe] at hgbc
    obtain ⟨h, hinvab⟩ := exists_smul_eq G (b : α) a
    rw [eq_comm, ← inv_smul_eq_iff] at hinvab
    rw [← hgbc, SetLike.val_smul, ← hinvab]
    rw [inv_smul_eq_iff, eq_comm]
    change h • g • h⁻¹ • a = a
    simp only [smul_smul, ← mul_assoc]
    rw [← mem_stabilizer_iff]
    apply hyp
    apply Subgroup.normalClosure_normal.conj_mem
    apply Subgroup.le_normalClosure
    exact hg

variable [Fintype α]

/-- A primitivity criterion -/
theorem IsPreprimitive.isPreprimitive_ofFixingSubgroup_inter
    {G : Type _} [Group G] [MulAction G α] {s : Set α}
    (hs : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s))
    {g : G} (ha : s ∪ g • s ≠ ⊤) : -- {a : α} (ha : a ∉ s ∪ g • s) :
    IsPreprimitive (fixingSubgroup G (s ∩ g • s))
      (SubMulAction.ofFixingSubgroup G (s ∩ g • s)) := by
  classical
  have hts : s ∩ g • s ≤ s := Set.inter_subset_left
  have this : IsPretransitive (fixingSubgroup G (s ∩ g • s))
      (SubMulAction.ofFixingSubgroup G (s ∩ g • s)) :=
    isPretransitive_ofFixingSubgroup_inter hs.toIsPretransitive ha

  apply isPreprimitive_of_large_image (f := SubMulAction.ofFixingSubgroup.mapOfInclusion G hts) hs

  rw [← Set.image_univ,
    Set.ncard_image_of_injective _ (SubMulAction.ofFixingSubgroup.mapOfInclusion_injective G _)]

  have this : Set.ncard (s ∩  g • s)ᶜ < 2 * Set.ncard (sᶜ) := by
    rw [Set.compl_inter, ← Nat.add_lt_add_iff_right, Set.ncard_union_add_ncard_inter]
    rw [← Set.compl_union, two_mul, add_assoc]
    simp only [add_lt_add_iff_left]
    rw [← add_lt_add_iff_left, Set.ncard_add_ncard_compl]
    rw [MulAction.smul_set_ncard_eq, ← add_assoc, Set.ncard_add_ncard_compl]
    simp only [lt_add_iff_pos_right]
    rw [Set.ncard_pos]
    rw [Set.nonempty_compl]
    exact ha
  convert this
  · rw [← Nat.card_eq_fintype_card, ← Set.Nat.card_coe_set_eq]
    rfl
  · rw [← SubMulAction.ofFixingSubgroup_carrier G]
    rw [← Set.ncard_image_of_injective (Set.univ) (SubMulAction.ofFixingSubgroup G s).inclusion_injective]
    rw [← SubMulAction.image_inclusion]
    congr
    simp only [Set.image_univ]

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


/-- A criterion due to Jordan for being 2-pretransitive (Wielandt, 13.1) -/
theorem is_two_pretransitive_weak_jordan [DecidableEq α]
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n.succ) (hsn' : 1 + n.succ < Fintype.card α)
    (hs_trans : IsPretransitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G α 2 := by
  revert α G
  induction' n using Nat.strong_induction_on with n hrec
  intro α G _ _ _ _ hG s hsn hsn' hs_trans

  have hs_ne_top : s ≠ ⊤ := by
    intro hs
    rw [hs, Set.top_eq_univ, Set.ncard_univ] at hsn
    rw [← hsn, Nat.card_eq_fintype_card, add_lt_iff_neg_right] at hsn'
    contradiction

  have hs_nonempty : s.Nonempty := by
    rw [← Set.ncard_pos, hsn]
    exact Nat.succ_pos n

  cases' Nat.lt_or_ge n.succ 2 with hn hn

  · -- Initialization : n = 0
    have hn : n = 0 := by
      rw [← le_zero_iff]
      apply Nat.le_of_succ_le_succ
      apply Nat.le_of_lt_succ
      exact hn

    simp only [hn, Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    rw [hsa] at hs_trans

    rw [stabilizer.isMultiplyPretransitive G α hG.toIsPretransitive]
    rw [← isPretransitive_iff_is_one_pretransitive]
    apply isPretransitive.of_surjective_map
      (SubMulAction.OfFixingSubgroupOfSingleton.map_bijective G a).surjective hs_trans

  -- The result is assumed by induction for sets of ncard ≤ n

  cases' Nat.lt_or_ge (2 * n.succ) (Fintype.card α) with hn1 hn2

  · -- CASE where 2 * s.ncard < fintype.card α
    -- get a, b ∈ s, a ≠ b
    have : 1 < s.ncard := by rw [hsn]; exact hn
    rw [Set.one_lt_ncard] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    -- apply Rudio's theorem to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ := Rudio hG s (Set.toFinite s) hs_nonempty hs_ne_top a b hab

    let t := s ∩ g • s
    have ht_trans : IsPretransitive (fixingSubgroup G t)
      (SubMulAction.ofFixingSubgroup G t) :=
        isPretransitive_ofFixingSubgroup_inter hs_trans (by
          apply Set.ncard_pigeonhole_compl'
          rw [smul_set_ncard_eq, hsn, ← two_mul]
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
    apply Set.ncard_ne_zero_of_mem (a := a)
    exact ⟨ha, hga⟩


  · -- CASE : 2 * s.ncard ≥ Fintype.card α
    have : Set.Nontrivial sᶜ := by
      rw [← Set.one_lt_ncard_iff_nontrivial]
      rw [← Nat.add_lt_add_iff_left, Set.ncard_add_ncard_compl]
      rw [Nat.card_eq_fintype_card, add_comm, hsn]
      exact hsn'
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨a, ha : a ∈ sᶜ, b, hb : b ∈ sᶜ, hab⟩ := this

    obtain ⟨g, hga, hgb⟩ := Rudio hG sᶜ (Set.toFinite sᶜ)
      (Set.nonempty_of_mem ha)
      (by intro h
          simp only [Set.top_eq_univ, Set.compl_univ_iff] at h
          simp only [h, Set.not_nonempty_empty] at hs_nonempty)
      a b hab
    let t := s ∩ g • s
    have : a ∉ s ∪ g • s := by
      rw [Set.mem_union]
      intro h
      cases' h with h h
      exact ha h
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hga h
      exact hga h
    have ht_trans : IsPretransitive (fixingSubgroup G t)
      (SubMulAction.ofFixingSubgroup G t) :=
        isPretransitive_ofFixingSubgroup_inter hs_trans
          (by intro h; apply this; rw [h]; trivial)
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
      constructor
      · apply Set.ncard_lt_ncard _ (Set.toFinite s)
        constructor
        apply Set.inter_subset_left
        intro h
        suffices s = g • s by
          apply hb
          rw [this]
          simp only [smul_compl_set, Set.mem_compl_iff, Set.not_not_mem] at hgb
          exact hgb
        apply Set.eq_of_subset_of_ncard_le
        · exact subset_trans h Set.inter_subset_right
        · rw [smul_set_ncard_eq]
        exact Set.toFinite (g • s)
      · rfl
    · rw [← Nat.pos_iff_ne_zero]
      -- variante de Set.ncard_pigeonhole qui utilise que la réunion n'est pas top
      apply Nat.lt_of_add_lt_add_right
      rw [Set.ncard_inter_add_ncard_union, zero_add, smul_set_ncard_eq,
        hsn, ← two_mul]
      apply lt_of_lt_of_le _ hn2
      rw [← not_le]
      intro h
      apply this
      convert Set.mem_univ a
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ Set.finite_univ
      simp only [Set.ncard_univ, Nat.card_eq_fintype_card]
      exact h

/- -- TODO : prove
theorem strong_jordan_of_preprimitive (hG : is_preprimitive G α)
  {s : set α} {n : ℕ} (hsn : fintype.card s = n.succ) (hsn' : 1 + n.succ < fintype.card α)
  (hs_prim : is_preprimitive (fixing_subgroup G s) (sub_mul_action.of_fixing_subgroup G s)) :
  is_multiply_preprimitive (subgroup.normal_closure (fixing_subgroup G s).carrier) α 2 := sorry
 -/

theorem is_two_preprimitive_weak_jordan [DecidableEq α]
    (hG : IsPreprimitive G α) {s : Set α} {n : ℕ}
    (hsn : s.ncard = n.succ) (hsn' : 1 + n.succ < Fintype.card α)
    (hs_prim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α 2 := by
  revert α G
  induction' n using Nat.strong_induction_on with n hrec
  intro α G _ _ _ _ hG s hsn hsn' hs_prim

  have hs_ne_top : s ≠ ⊤ := by
    intro hs
    rw [hs, Set.top_eq_univ, Set.ncard_univ] at hsn
    rw [← hsn, Nat.card_eq_fintype_card, add_lt_iff_neg_right] at hsn'
    contradiction

  have hs_nonempty : s.Nonempty := by
    rw [← Set.ncard_pos, hsn]
    exact Nat.succ_pos n

  -- The result is assumed by induction for sets of ncard ≤ n

  cases' Nat.lt_or_ge n.succ 2 with hn hn

  · -- When n < 2 (imposes n = 0)
    have hn : n = 0 := by
      rw [← le_zero_iff]
      apply Nat.le_of_succ_le_succ
      apply Nat.le_of_lt_succ
      exact hn

    simp only [hn, Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    rw [hsa] at hs_prim

    rw [stabilizer.isMultiplyPreprimitive G α (Nat.le_refl 1) hG.toIsPretransitive]
    rw [← isPreprimitive_iff_is_one_preprimitive]
    apply isPreprimitive_of_surjective_map
      (SubMulAction.OfFixingSubgroupOfSingleton.map_bijective G a).surjective hs_prim

  cases' Nat.lt_or_ge (2 * n.succ) (Fintype.card α) with hn1 hn2

  · -- CASE where 2 * s.ncard < fintype.card α
    -- get a, b ∈ s, a ≠ b
    have : 1 < s.ncard := by rw [hsn]; exact hn
    rw [Set.one_lt_ncard] at this
    obtain ⟨a, ha, b, hb, hab⟩ := this
    -- apply rudio to get g ∈ G such that a ∈ g • s, b ∉ g • s
    obtain ⟨g, hga, hgb⟩ := Rudio hG s (Set.toFinite s) hs_nonempty hs_ne_top a b hab

    let t := s ∩ g • s
    have ht_prim : IsPreprimitive (fixingSubgroup G t)
      (SubMulAction.ofFixingSubgroup G t) :=
        hs_prim.isPreprimitive_ofFixingSubgroup_inter (by
          apply Set.ncard_pigeonhole_compl'
          rw [smul_set_ncard_eq, hsn, ← two_mul]
          exact hn1)
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
      rw [← Set.one_lt_ncard_iff_nontrivial]
      rw [← Nat.add_lt_add_iff_left, Set.ncard_add_ncard_compl]
      rw [Nat.card_eq_fintype_card, add_comm, hsn]
      exact hsn'
    -- get a, b ∈ sᶜ, a ≠ b
    obtain ⟨a, ha : a ∈ sᶜ, b, hb : b ∈ sᶜ, hab⟩ := this

    obtain ⟨g, hga, hgb⟩ := Rudio hG sᶜ (Set.toFinite sᶜ)
      (Set.nonempty_of_mem ha)
      (by intro h
          simp only [Set.top_eq_univ, Set.compl_univ_iff] at h
          simp only [h, Set.not_nonempty_empty] at hs_nonempty)
      a b hab
    let t := s ∩ g • s
    have : a ∉ s ∪ g • s := by
      rw [Set.mem_union]
      intro h
      cases' h with h h
      exact ha h
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hga h
      exact hga h
    have ht_prim : IsPreprimitive (fixingSubgroup G t)
      (SubMulAction.ofFixingSubgroup G t) :=
        hs_prim.isPreprimitive_ofFixingSubgroup_inter
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
    suffices t.ncard ≠ 0 by
      rw [← Nat.succ_lt_succ_iff, ← hsn, Nat.succ_pred this]
      constructor
      · apply Set.ncard_lt_ncard _ (Set.toFinite s)
        constructor
        apply Set.inter_subset_left
        intro h
        suffices s = g • s by
          apply hb
          rw [this]
          simp only [smul_compl_set, Set.mem_compl_iff, Set.not_not_mem] at hgb
          exact hgb
        apply Set.eq_of_subset_of_ncard_le
        · exact subset_trans h Set.inter_subset_right
        · rw [smul_set_ncard_eq]
        exact Set.toFinite (g • s)
      · rfl
    · rw [← Nat.pos_iff_ne_zero]
      -- variante de Set.ncard_pigeonhole qui utilise que la réunion n'est pas top
      apply Nat.lt_of_add_lt_add_right
      rw [Set.ncard_inter_add_ncard_union, zero_add, smul_set_ncard_eq,
        hsn, ← two_mul]
      apply lt_of_lt_of_le _ hn2
      rw [← not_le]
      intro h
      apply this
      convert Set.mem_univ a
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ Set.finite_univ
      simp only [Set.ncard_univ, Nat.card_eq_fintype_card]
      exact h

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
    (hsn : s.ncard = n.succ) (hsn' : 1 + n.succ < Fintype.card α)
    (hprim : IsPreprimitive (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s)) :
    IsMultiplyPreprimitive G α (1 + n.succ) := by
  classical
  revert α G
  induction' n with n hrec

  · -- case n = 0
    intro α G _ _ _ hG s hsn _ hGs
    haveI : IsPretransitive G α := hG.toIsPretransitive
    simp only [Set.ncard_eq_one] at hsn
    obtain ⟨a, hsa⟩ := hsn
    rw [hsa] at hGs

    constructor
    · rw [stabilizer.isMultiplyPretransitive]
      rw [← isPretransitive_iff_is_one_pretransitive]
      apply isPretransitive.of_surjective_map
        (SubMulAction.OfFixingSubgroupOfSingleton.map_bijective G a).surjective
        hGs.toIsPretransitive
      exact hG.toIsPretransitive
    · intro t h
      simp only [Nat.zero_eq, Nat.cast_add, Nat.cast_one] at h
      rw [← Nat.cast_one, WithTop.add_eq_add_iff, Nat.cast_one] at h
      obtain ⟨b, htb⟩ := Set.encard_eq_one.mp h
      obtain ⟨g, hg⟩ := exists_smul_eq G a b
      have hst : g • ({a} : Set α) = ({b} : Set α) := by
        change (fun x => g • x) '' {a} = {b}
        rw [Set.image_singleton, hg]
      rw [htb]
      refine isPreprimitive_of_surjective_map
        (SubMulAction.conjMap_ofFixingSubgroup_bijective G hst).surjective hGs

  -- Induction step
  intro α G _ _ _ hG s hsn hα hGs
  suffices ∃ (a : α) (t : Set (SubMulAction.ofStabilizer G a)),
    a ∈ s ∧ s = insert a (Subtype.val '' t) by
    obtain ⟨a, t, _, hst⟩ := this
    have ha' : a ∉ Subtype.val '' t := by
      intro h; rw [Set.mem_image] at h ; obtain ⟨x, hx⟩ := h
      apply x.prop; rw [hx.right]; exact Set.mem_singleton a
    have ht_prim : IsPreprimitive (stabilizer G a) (SubMulAction.ofStabilizer G a) := by
      rw [isPreprimitive_iff_is_one_preprimitive]
      rw [← stabilizer.isMultiplyPreprimitive G α (Nat.le_refl 1) hG.toIsPretransitive]
      apply is_two_preprimitive_weak_jordan hG hsn hα hGs
    have hGs' : IsPreprimitive (fixingSubgroup (stabilizer G a) t)
      (SubMulAction.ofFixingSubgroup (stabilizer G a) t) :=  by
      apply isPreprimitive_of_surjective_map
        (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective G a t).surjective
      apply isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupOfEq.map_bijective G hst).surjective
      exact hGs
    rw [← Nat.succ_eq_one_add]
    rw [stabilizer.isMultiplyPreprimitive G α _ hG.toIsPretransitive]
    suffices n + 2 = 1 + Nat.succ n by
      rw [this]
      refine hrec ht_prim ?_ ?_ hGs'
      · -- t.card = Nat.succ n
        rw [← Set.ncard_image_of_injective t Subtype.val_injective]
        apply Nat.add_right_cancel
        rw [← Set.ncard_insert_of_not_mem ha', ← hst, hsn]
      · -- 1 + n.succ < Fintype.card (SubMulAction.ofStabilizer G α a)
        change _ < Fintype.card (SubMulAction.ofStabilizer G a).carrier
        rw [← Nat.card_eq_fintype_card, Set.Nat.card_coe_set_eq]
        rw [SubMulAction.ofStabilizer_carrier]
        rw [← Nat.succ_eq_one_add]
        apply Nat.lt_of_add_lt_add_left
        rw [Set.ncard_add_ncard_compl]
        simp only [Set.ncard_singleton, Nat.card_eq_fintype_card]
        exact hα
    · exact Nat.succ_eq_one_add (n + 1)
    · apply Nat.succ_le_succ; apply Nat.zero_le
  -- ∃ (a : α), a ∈ s
  suffices s.Nonempty by
    obtain ⟨a, ha⟩ := this
    use a
    use Subtype.val ⁻¹' s
    apply And.intro ha

--
    rw [Set.image_preimage_eq_inter_range]
    rw [Set.insert_eq]
    simp only [Subtype.range_coe_subtype, Set.singleton_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    simp_rw [SubMulAction.mem_ofStabilizer_iff]
    simp only [Ne]
    ext x
    --    apply subset_antisymm,
    · rw [Set.mem_insert_iff]
      simp
      rw [or_and_left]
      simp_rw [or_not]
      rw [and_true]
      constructor
      intro hx; apply Or.intro_right _ hx
      intro hx; cases' hx with hx hx
      rw [hx]; exact ha
      exact hx
  rw [← Set.ncard_pos, hsn]
  apply Nat.succ_pos

end Jordan

section Subgroups

variable {α : Type _} [Fintype α]

variable {G : Subgroup (Equiv.Perm α)}

theorem eq_s2_of_nontrivial (hα : Fintype.card α ≤ 2) (hG : Nontrivial G) :
    G = (⊤ : Subgroup (Equiv.Perm α)) := by
  classical
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_subtype_le
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [Fintype.card_equiv (Equiv.cast rfl)]
    trans (2 : ℕ).factorial
    · exact Nat.factorial_le hα
    rw [Nat.factorial_two]
    rw [← Fintype.one_lt_card_iff_nontrivial] at hG
    exact hG

theorem nontrivial_on_equiv_perm_two {K : Type _} [Group K] [MulAction K α]
    (hα : Fintype.card α = 2) {g : K} {a : α} (hga : g • a ≠ a) : IsMultiplyPretransitive K α 2 := by
  classical
  let φ := MulAction.toPermHom K α
  let f : α →ₑ[φ] α :=
    { toFun := id
      map_smul' := fun k x => rfl }
  have hf : Function.Bijective f := Function.bijective_id
  suffices Function.Surjective φ by
    rw [isMultiplyPretransitive_of_bijective_map_iff this hf]
    rw [← hα]
    apply Equiv.Perm.isMultiplyPretransitive

  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  apply le_antisymm
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_subtype_le
  suffices hg : toPerm g ∈ φ.range by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [Fintype.card_perm, hα, Nat.factorial_two, Nat.succ_le_iff,
      ← Nat.card_eq_fintype_card, Subgroup.one_lt_card_iff_ne_bot]
    intro h; apply hga
    rw [h, Subgroup.mem_bot] at hg
    rw [← MulAction.toPerm_apply, hg, Equiv.Perm.coe_one, id_eq]
  use g
  rfl

theorem isPretransitive_of_cycle [DecidableEq α] {g : Equiv.Perm α}
    (hg : g ∈ G) (hgc : g.IsCycle) :
    IsPretransitive (fixingSubgroup G ((↑g.support : Set α)ᶜ))
      (SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ)) := by
  obtain ⟨a, _, hgc⟩ := hgc
  have hs : ∀ x : α, g • x ≠ x ↔
    x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ) := by
    intro x
    rw [SubMulAction.mem_ofFixingSubgroup_iff]
    simp only [Set.mem_compl_iff, Finset.mem_coe, Equiv.Perm.not_mem_support]
    rfl
  suffices ∀ x ∈ SubMulAction.ofFixingSubgroup G ((↑g.support : Set α)ᶜ),
      ∃ k : fixingSubgroup G ((↑g.support : Set α)ᶜ), x = k • a
    by
    apply IsPretransitive.mk
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨k, hk⟩ := this x hx
    obtain ⟨k', hk'⟩ := this y hy
    use k' * k⁻¹
    rw [← SetLike.coe_eq_coe]
    simp only [SetLike.mk_smul_mk]
    rw [hk, hk', smul_smul, inv_mul_cancel_right]
  intro x hx
  have hg' : (⟨g, hg⟩ : ↥G) ∈ fixingSubgroup G ((↑g.support : Set α)ᶜ) :=
    by
    simp_rw [mem_fixingSubgroup_iff G]
    intro y hy
    simpa only [Set.mem_compl_iff, Finset.mem_coe, Equiv.Perm.not_mem_support] using hy
  let g' : fixingSubgroup (↥G) ((↑g.support : Set α)ᶜ) := ⟨(⟨g, hg⟩ : ↥G), hg'⟩
  obtain ⟨i, hi⟩ := hgc ((hs x).mpr hx)
  use g' ^ i; exact hi.symm

theorem Equiv.Perm.IsSwap.cycleType [DecidableEq α] {σ : Equiv.Perm α} (h : σ.IsSwap) :
    σ.cycleType = {2} := by
  simp only [h.isCycle.cycleType, Equiv.Perm.card_support_eq_two.mpr h]
  simp only [Multiset.coe_singleton]

theorem Equiv.Perm.IsSwap.orderOf [DecidableEq α] {σ : Equiv.Perm α} (h : σ.IsSwap) :
    orderOf σ = 2 := by
  rw [← Equiv.Perm.lcm_cycleType, h.cycleType, Multiset.lcm_singleton, normalize_eq]

/-- A primitive permutation group that contains a swap is the full permutation group (Jordan)-/
theorem jordan_swap [DecidableEq α] (hG : IsPreprimitive G α) (g : Equiv.Perm α)
    (h2g : Equiv.Perm.IsSwap g) (hg : g ∈ G) : G = ⊤ := by
  classical
  cases' Nat.lt_or_ge (Fintype.card α) 3 with hα3 hα3
  · -- trivial case : Fintype.card α ≤ 2
    rw [Nat.lt_succ_iff] at hα3
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply le_antisymm (Fintype.card_subtype_le _)
    rw [Fintype.card_equiv (Equiv.cast rfl)]
    refine le_trans (Nat.factorial_le hα3) ?_
    rw [Nat.factorial_two]
    have : Nonempty G := One.instNonempty
    apply Nat.le_of_dvd Fintype.card_pos
    rw [← h2g.orderOf, orderOf_submonoid ⟨g, hg⟩]
    exact orderOf_dvd_card
  -- important case : Fintype.card α ≥ 3
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hα3
  rw [add_comm] at hn
  -- let s := (g.support : Set α)
  have hsc : Set.ncard ((g.support)ᶜ : Set α) = n.succ := by
    apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Set.ncard_coe_Finset, Equiv.Perm.card_support_eq_two.mpr h2g, add_comm, hn]
  apply IsMultiplyPretransitive.eq_top_of_is_full_minus_one_pretransitive
  apply IsMultiplyPreprimitive.toIsMultiplyPretransitive
  have hn' : Fintype.card α - 1 = 1 + n.succ := by
    rw [hn, add_comm 1]
    simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, add_eq_zero, and_false, tsub_zero]
  rw [hn']
  refine isMultiplyPreprimitive_jordan hG hsc ?_ ?_
  · rw [← hn']
    apply Nat.sub_lt _ (by norm_num)
    apply lt_of_lt_of_le (by norm_num) hα3
  have : IsPretransitive _ _ := isPretransitive_of_cycle hg <| Equiv.Perm.IsSwap.isCycle h2g
  apply isPreprimitive_of_prime
  convert Nat.prime_two
  rw [Fintype.card_subtype]
  rw [← Equiv.Perm.card_support_eq_two.mpr h2g]
  apply congr_arg
  ext x
  simp only [SubMulAction.mem_ofFixingSubgroup_iff, Set.mem_compl_iff, Finset.mem_coe,
    Equiv.Perm.mem_support, ne_eq, not_not, Finset.mem_univ, forall_true_left,
    Finset.mem_filter, true_and]

/-- A primitive permutation that contains a 3-cycle contains the alternating group (Jordan) -/
theorem jordan_three_cycle [DecidableEq α]
    (hG : IsPreprimitive G α) {g : Equiv.Perm α}
    (h3g : Equiv.Perm.IsThreeCycle g) (hg : g ∈ G) :
    alternatingGroup α ≤ G := by
  classical
  cases' Nat.lt_or_ge (Fintype.card α) 4 with hα4 hα4
  · -- trivial case : Fintype.card α ≤ 3
    rw [Nat.lt_succ_iff] at hα4
    apply large_subgroup_of_perm_contains_alternating
    rw [Fintype.card_perm]
    apply le_trans (Nat.factorial_le hα4)
    change 2 * 3 ≤ _
    simp only [mul_le_mul_left, Nat.succ_pos']
    have : Nonempty G := One.instNonempty
    apply Nat.le_of_dvd Fintype.card_pos
    suffices 3 = orderOf (⟨g, hg⟩ : G) by
      rw [this]
      exact orderOf_dvd_card
    rw [← Equiv.Perm.IsThreeCycle.orderOf h3g]
    convert orderOf_submonoid _
    rfl
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hα4; rw [add_comm] at hn
  --  refine is_full_minus_two_pretransitive_iff α _,
  apply IsMultiplyPretransitive.alternatingGroup_le_of_sub_two
  apply IsMultiplyPreprimitive.toIsMultiplyPretransitive
  -- suffices : IsMultiplyPreprimitive G α (Fintype.card α - 2)
  -- apply this.left.alternatingGroup_le_of_sub_two
  have hn' : Fintype.card α - 2 = 1 + n.succ :=  by
    simp [hn, add_comm 1]
  rw [hn']
  refine isMultiplyPreprimitive_jordan (s := (g.supportᶜ : Set α)) hG ?_ ?_ ?_
  · apply Nat.add_left_cancel
    rw [Set.ncard_add_ncard_compl, Set.ncard_coe_Finset,
      Equiv.Perm.IsThreeCycle.card_support h3g,
      add_comm, Nat.card_eq_fintype_card, hn]
  · rw [hn, Nat.succ_eq_add_one, add_comm, add_assoc]
    simp only [add_lt_add_iff_left]
    norm_num
  have : IsPretransitive _ _ := isPretransitive_of_cycle hg <| Equiv.Perm.IsThreeCycle.isCycle h3g
  apply isPreprimitive_of_prime
  convert Nat.prime_three
  rw [Fintype.card_subtype, ← Equiv.Perm.IsThreeCycle.card_support h3g]
  apply congr_arg
  ext x
  simp [SubMulAction.mem_ofFixingSubgroup_iff]

/- -- TODO : prove
theorem jordan_prime_cycle [decidable_eq α] (hG : is_preprimitive G α)
  {p : nat} (hp : prime p) (hp' : p + 3 ≤ fintype.card α)
  {g : equiv.perm α} (hgc : equiv.perm.is_cycle g) (hgp : fintype.card g.support = p)
  (hg : g ∈ G) : alternating_group α ≤ G := sorry
 -/
end Subgroups

#lint
