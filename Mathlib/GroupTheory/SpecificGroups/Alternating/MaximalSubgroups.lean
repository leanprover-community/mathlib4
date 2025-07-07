/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.MaximalSubgroups
import Mathlib.GroupTheory.SpecificGroups.Alternating
/-! # Maximal subgroups of the alternating group -/

/-
import Jordan.Mathlib.Alternating
import Jordan.IndexNormal
import Jordan.Primitive
import Jordan.MultipleTransitivity
import Jordan.StabilizerPrimitive
import Jordan.PermIwasawa
import Jordan.PermMaximal
import Jordan.V4
-/

open scoped Pointwise

open MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace alternatingGroup

theorem isPretransitive_ofFixingSubgroup (s : Set α) (h0 : s.Nontrivial)
    (hα : Set.ncard s < Set.ncard (sᶜ : Set α)) :
    IsPretransitive (fixingSubgroup (alternatingGroup α) s)
      (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) := by
  rw [← is_one_pretransitive_iff]
  apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (Hn := ?_) (hmn := rfl)
  have _ := AlternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2)
  · have h1' : 2 < Set.ncard (sᶜ : Set α) := by
      apply lt_of_le_of_lt _ hα
      rw [Nat.succ_le_iff, Set.one_lt_ncard]
      exact h0
    rw [add_comm, ← Set.ncard_add_ncard_compl s,
      Nat.add_sub_assoc (le_of_lt h1'), add_comm 1, add_le_add_iff_left]
    apply Nat.le_sub_of_add_le
    exact h1'
  · exact Nat.sub_le (Nat.card α) 2

theorem _root_.Equiv.Perm.swap_mul_swap_mem_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    {g g' : Equiv.Perm α} (hg : Equiv.Perm.IsSwap g) (hg' : Equiv.Perm.IsSwap g') :
    g * g' ∈ alternatingGroup α := by
  simp [Equiv.Perm.mem_alternatingGroup, map_mul, hg.sign_eq, hg'.sign_eq]

/-- If `s : Set α` is nonempty and its complement has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
theorem stabilizer_ne_top (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  rw [Set.mem_compl_iff] at hb hc
  have hac : a ≠ c := ne_of_mem_of_not_mem ha hc
  have hab : a ≠ b := ne_of_mem_of_not_mem ha hb
  intro h; apply hc
  let g := Equiv.swap a b * Equiv.swap a c
  suffices g • s = s by
    rw [← this]
    use a, ha
    dsimp [g]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hg : g ∈ alternatingGroup α := by
    rw [← Equiv.Perm.swap_isSwap_iff] at hab hac
    exact Equiv.Perm.swap_mul_swap_mem_alternatingGroup hab hac
  rw [← Subgroup.mk_smul g hg, ← MulAction.mem_stabilizer_iff, h]
  apply Subgroup.mem_top

/-- If `s : Set α` is nonempty, as well as its complement,
and one of `s`, `sᶜ` has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
theorem stabilizer_ne_top' (s : Set α) (hs : s.Nonempty) (hsc : sᶜ.Nonempty)
    (hssc : s.Nontrivial ∨ (sᶜ : Set α).Nontrivial) : stabilizer (alternatingGroup α) s ≠ ⊤ := by
  rcases hssc with hs' | hsc'
  · rw [← stabilizer_compl]
    rw [← compl_compl s] at hs'
    exact stabilizer_ne_top (sᶜ) hsc hs'
  exact stabilizer_ne_top s hs hsc'

-- Il va falloir, soit que t ait ≥ 3 éléments, soit que tᶜ en ait ≥ 2.
-- autrement dit : fintype.card α ≥ 4.
-- La condition est nécessaire :
-- dans le cas α = {1, 2, 3}, t = {1,2} ou t = {1}, le résultat est faux
theorem moves_in (hα : 4 ≤ Fintype.card α) (t : Set α) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g ∈ stabilizer (Equiv.Perm α) t ⊓ alternatingGroup α, g • a = b := by
  intro a ha b hb
  by_cases hab : a = b
  · -- a = b, on prend g = 1,
    use 1
    simp only [hab, Subgroup.one_mem, one_smul, and_self]
  · rw [← Ne] at hab
    rcases le_or_gt (Set.ncard t) 2 with ht | ht'
    · -- fintype.card t ≤ 2, alors on prend le produit d'un swap (a b) avec un swap dans tᶜ
      have h : 1 < Set.ncard (tᶜ : Set α) := by
        by_contra h
        rw [not_lt] at h
        rw [← not_lt] at hα
        apply hα
        rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl t]
        apply Nat.lt_succ_of_le
        apply add_le_add ht h
      rw [Set.one_lt_ncard_iff] at h
      obtain ⟨c, d, hc, hd, hcd⟩ := h
      simp only [Ne] at hcd
      use Equiv.swap a b * Equiv.swap c d
      constructor
      · simp only [Subgroup.mem_inf]
        constructor
        · rw [mem_stabilizer_set_iff_subset_smul_set t.toFinite, Set.subset_smul_set_iff]
          rintro _ ⟨x, hx, rfl⟩
          simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.smul_def, Equiv.Perm.coe_mul,
            Function.comp_apply]
          by_cases hxa : x = a
          · rwa [hxa, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne]
            · apply ne_of_mem_of_not_mem hb hc
            · apply ne_of_mem_of_not_mem hb hd
          · by_cases hxb : x = b
            · rwa [hxb, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
              · apply ne_of_mem_of_not_mem ha hc
              · apply ne_of_mem_of_not_mem ha hd
            · rwa [Equiv.swap_apply_of_ne_of_ne hxa hxb, Equiv.swap_apply_of_ne_of_ne]
              · apply ne_of_mem_of_not_mem hx hc
              · apply ne_of_mem_of_not_mem hx hd
        · simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
          rw [Equiv.Perm.sign_swap hab]; rw [Equiv.Perm.sign_swap hcd]
          simp only [Int.units_mul_self]
      · simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
        rw [Set.mem_compl_iff t] at hc hd
        have hac : a ≠ c := by intro h; apply hc; rw [← h]; exact ha
        have had : a ≠ d := by intro h; apply hd; rw [← h]; exact ha
        rw [Equiv.swap_apply_of_ne_of_ne hac had]
        rw [Equiv.swap_apply_left]
    · -- fintype t ≥ 3, alors on prend un 3-cycle dans t
      suffices ∃ c ∈ t, c ≠ a ∧ c ≠ b by
        obtain ⟨c, hc, hca, hcb⟩ := this
        use Equiv.swap a c * Equiv.swap a b
        constructor
        · simp only [Subgroup.mem_inf]
          constructor
          · rw [mem_stabilizer_set_iff_subset_smul_set t.toFinite, Set.subset_smul_set_iff]
            rintro _ ⟨x, hx, rfl⟩
            · simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.smul_def, Equiv.Perm.coe_mul,
                Function.comp_apply]
              by_cases hxa : x = a
              · rwa [hxa, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb]
              · rw [← Ne] at hxa
                by_cases hxc : x = c
                · rwa [hxc, Equiv.swap_apply_right, Equiv.swap_apply_left]
                · rw [← Ne] at hxc
                  rw [Equiv.swap_apply_of_ne_of_ne hxa hxc]
                  by_cases hxc : x = b
                  · rw [hxc, Equiv.swap_apply_right]; exact ha
                  · rw [← Ne] at hxc
                    rw [Equiv.swap_apply_of_ne_of_ne hxa hxc]
                    exact hx
          · simp only [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
            rw [Equiv.Perm.sign_swap hab]; rw [Equiv.Perm.sign_swap (Ne.symm hca)]
            simp only [Int.units_mul_self]
        · simp only [Equiv.Perm.smul_def, Equiv.Perm.coe_mul, Function.comp_apply]
          rw [Equiv.swap_apply_left]
          rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
      suffices (t \ {a, b}).Nonempty by
        obtain ⟨c, h⟩ := this
        simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
        use c
  -- apply And.intro h.left
  -- exact h.right
      rw [Set.diff_nonempty]
      intro ht
      rw [← not_le] at ht'
      apply ht'
      convert Set.ncard_le_ncard ht
      rw [(Set.ncard_pair hab).symm]

theorem moves_in' (hα : 4 ≤ Fintype.card α) (G : Subgroup (Equiv.Perm α)) (t : Set α)
    (hGt : stabilizer (Equiv.Perm α) t ⊓ alternatingGroup α ≤ G) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g : G, g • a = b := by
  intro a ha b hb
  obtain ⟨g, hg, H⟩ := moves_in hα t a ha b hb
  use! g, hGt hg, H

theorem has_three_cycle_of_stabilizer' (s : Set α) (hs : 2 < Set.ncard s) :
    ∃ g : Equiv.Perm α, g.IsThreeCycle ∧ g ∈ stabilizer (Equiv.Perm α) s := by
  rw [Set.two_lt_ncard_iff] at hs
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hs
  use Equiv.swap a b * Equiv.swap a c
  constructor
  · apply Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  rw [← stabilizer_compl]
  rw [mem_stabilizer_set_iff_subset_smul_set sᶜ.toFinite, Set.subset_smul_set_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [mul_inv_rev, Equiv.swap_inv, Equiv.Perm.smul_def, Equiv.Perm.coe_mul,
    Function.comp_apply, Set.mem_compl_iff]
  rw [Set.mem_compl_iff] at hx
  suffices h : ∀ u ∈ s, x ≠ u by
    rw [Equiv.swap_apply_of_ne_of_ne (h a ha) (h b hb)]
    rw [Equiv.swap_apply_of_ne_of_ne (h a ha) (h c hc)]
    exact hx
  grind  -- since x ∉ s, x ≠ u, for any u ∈ s

omit [DecidableEq α] in
theorem has_three_cycle_of_stabilizer [DecidableEq α] (s : Set α) (hα : 4 < Fintype.card α) :
    ∃ g : Equiv.Perm α, g.IsThreeCycle ∧ g ∈ stabilizer (Equiv.Perm α) s := by
  rcases Nat.lt_or_ge 2 (Set.ncard s) with hs | hs
  · exact has_three_cycle_of_stabilizer' s hs
  · suffices hs' : _ by
      obtain ⟨g, hg, hg'⟩ := has_three_cycle_of_stabilizer' (sᶜ) hs'
      use g
      rw [stabilizer_compl] at hg'
      exact ⟨hg, hg'⟩
    rw [lt_iff_not_ge] at hα ⊢
    intro hs'; apply hα
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s]
    exact Nat.add_le_add hs hs'

theorem le_of_isPreprimitive (s : Set α) (hα : 4 < Fintype.card α)
    (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G)
    (hG' : IsPreprimitive G α) :
    alternatingGroup α ≤ G := by
  -- We need to prove that alternating_group α ≤ ⊤
  -- G contains a three_cycle
  obtain ⟨g, hg3, hg⟩ := has_three_cycle_of_stabilizer s hα
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply jordan_three_cycle hG' hg3
  apply hG
  simp only [Subgroup.mem_inf, hg, true_and]
  exact Equiv.Perm.IsThreeCycle.mem_alternatingGroup hg3

theorem isPreprimitive_of_stabilizer_lt (s : Set α)
    (h0 : s.Nontrivial) (h1 : sᶜ.Nontrivial)
    (hα : Set.ncard s < Set.ncard (sᶜ : Set α)) (h4 : 4 ≤ Fintype.card α)
    (G : Subgroup (Equiv.Perm α))
    (hG : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α < G ⊓ alternatingGroup α) :
    IsPreprimitive G α := by
  -- G acts transitively
  have : IsPretransitive G α := by
    have hG' : stabilizer (Equiv.Perm α) s ⊓ alternatingGroup α ≤ G :=
      le_trans (le_of_lt hG) inf_le_left
    apply Equiv.Perm.IsPretransitive.of_partition G (s := s)
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := moves_in h4 s a ha b hb
      use! g
      exact hG' hg
      exact H
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := moves_in h4 (sᶜ) a ha b hb
      use! g
      apply hG'
      rw [stabilizer_compl] at hg ; exact hg
      exact H
    · intro h
      apply (lt_iff_le_not_ge.mp hG).right
      --  G ⊓ alternating_group α ≤ stabilizer (equiv.perm α) s ⊓ alternating_group α,
      rw [le_inf_iff]
      constructor
      · intro g
        rw [Subgroup.mem_inf, mem_stabilizer_iff]
        rintro ⟨hg, _⟩
        rw [← Subgroup.coe_mk G g hg]
        change (⟨g, hg⟩ : ↥G) • s = s
        rw [← mem_stabilizer_iff, h]
        exact Subgroup.mem_top _
      · exact inf_le_right
  apply IsPreprimitive.mk
  -- The proof needs 4 steps
  /- Step 1 : No block is equal to sᶜ
       This uses that fintype.card s < fintype.card sᶜ.
       In the equality case, fintype.card s = fintype.card sᶜ, it is possible that B = sᶜ,
       then G is the wreath product,
       this is case (b) of the O'Nan-Scott classification of max'l subgroups of the symmetric group -/
  have hB_ne_sc : ∀ (B : Set α) (_ : IsBlock G B), ¬B = sᶜ := by
    intro B hB hBsc
    obtain ⟨b, hb⟩ := h1.nonempty; rw [← hBsc] at hb
    obtain ⟨a, ha⟩ := h0.nonempty
    obtain ⟨k, hk⟩ := exists_smul_eq G b a
    suffices Set.ncard (B : Set α) ≤ Set.ncard s by
      apply Nat.lt_irrefl (Set.ncard B)
      apply lt_of_le_of_lt this
      simp_rw [hBsc]; exact hα
    rw [← Set.ncard_smul_set k B]
    apply Set.ncard_le_ncard (ht := Set.toFinite s)
    rw [← Set.disjoint_compl_right_iff_subset, ← hBsc]
    apply or_iff_not_imp_left.mp (IsBlock.def_one.mp hB k)
    intro h
    apply Set.not_mem_empty a
    rw [← Set.inter_compl_self s]
    constructor
    · exact ha
    · rw [← hk, ← hBsc, ← h, Set.smul_mem_smul_set_iff]
      exact hb

  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc : ∀ (B : Set α) (_ : IsBlock G B) (_ : B ⊆ sᶜ), B.Subsingleton := by
    intro B hB hBsc
    rw [← Equiv.Perm.Subtype.image_preimage_of_val hBsc]
    apply Set.Subsingleton.image
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)) by
      apply Or.resolve_right this
      intro hB'
      apply hB_ne_sc B hB
      simp only [Set.top_eq_univ, Set.preimage_eq_univ_iff, Subtype.range_coe_subtype] at hB'
      apply Set.Subset.antisymm hBsc hB'
    -- is_trivial_block (coe ⁻¹' B : set (sᶜ : set α)),
    suffices IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α) by
      refine IsPreprimitive.has_trivial_blocks this ?_
      -- is_block (coe ⁻¹' B : set (sᶜ : set α))
      let φ' : stabilizer G (sᶜ : Set α) → G := Subtype.val
      let f' : (sᶜ : Set α) →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun m x => by simp only [φ', SMul.smul_stabilizer_def] }
      apply MulAction.IsBlock_preimage f' hB
    apply stabilizer.isPreprimitive'
    · rw [compl_compl]; exact h0
    · rw [stabilizer_compl]
      convert le_trans (le_of_lt hG) inf_le_left

 -- Step 3 : A block contained in s is a subsingleton
  have hB_not_le_s : ∀ (B : Set α) (_ : IsBlock G B), B ⊆ s → B.Subsingleton := by
    intro B hB hBs
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
      cases' this with hB' hB'
      · -- trivial case
        rw [← Equiv.Perm.Subtype.image_preimage_of_val hBs]
        apply Set.Subsingleton.image
        exact hB'
      · -- coe ⁻¹' B = s
        have hBs' : B = s := by
          apply Set.Subset.antisymm hBs
          intro x hx
          suffices x = Subtype.val (⟨x, hx⟩ : s) by
            rw [this, ← Set.mem_preimage, hB', Set.top_eq_univ]
            apply Set.mem_univ
          rfl
        have : ∃ g' ∈ G, g' • s ≠ s := by
          by_contra h
          push_neg at h
          apply ne_of_lt hG
          apply le_antisymm (le_of_lt hG)
          intro g' hg'
          rw [Subgroup.mem_inf] at hg' ⊢
          exact ⟨h g' hg'.left, hg'.right⟩
        obtain ⟨g', hg', hg's⟩ := this
        cases' IsBlock.def_one.mp hB ⟨g', hg'⟩ with h h
        · -- case g' • B = B : absurd, since B = s and choice of g'
          exfalso
          apply hg's; rw [← hBs']; exact h
        · -- case g' • B disjoint from B
          suffices (g' • B).Subsingleton by
            apply Set.subsingleton_of_image _ B this
            apply Function.Bijective.injective (MulAction.bijective _)
          apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B) (IsBlock_of_block _ hB)
          rw [← hBs']
          exact Disjoint.subset_compl_right h
    -- is_trivial_block (coe ⁻¹' B : set s),
    suffices IsPreprimitive (stabilizer G s) (s : Set α) by
      refine IsPreprimitive.has_trivial_blocks this ?_
      -- is_block (coe ⁻¹' B : set s)
      let φ' : stabilizer G s → G := Subtype.val
      let f' : s →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by simp [φ'] }
      apply MulAction.IsBlock_preimage f' hB
    apply stabilizer.isPreprimitive' s h1
    convert le_trans (le_of_lt hG) inf_le_left
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'
  obtain ⟨a, ha, ha'⟩ := Set.not_subset_iff_exists_mem_not_mem.mp
    fun h => hB' ((hB_not_le_sc B hB) h)
  rw [Set.not_mem_compl_iff] at ha'
  obtain ⟨b, hb, hb'⟩ := Set.not_subset_iff_exists_mem_not_mem.mp
    fun h => hB' ((hB_not_le_s B hB) h)
  rw [← Set.mem_compl_iff] at hb'
  have hsc_le_B : sᶜ ⊆ B := by
    intro x hx'
    suffices ∃ k : fixingSubgroup (alternatingGroup α) s, k • b = x by
      obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
      suffices k • B = B by
        rw [← hkbx, ← this, Set.smul_mem_smul_set_iff]
        exact hb
      -- k • B = B,
      apply or_iff_not_imp_right.mp (IsBlock.def_one.mp hB ⟨k, _⟩)
      rw [Set.not_disjoint_iff_nonempty_inter]
      change (k • B ∩ B).Nonempty
      use a
      constructor
      · rw [mem_fixingSubgroup_iff] at hk
        rw [← hk a ha']
        exact Set.smul_mem_smul_set ha
      · exact ha
      · -- ↑k ∈ G
        apply le_trans (le_of_lt hG); exact inf_le_left
        rw [Subgroup.mem_inf]; constructor
        suffices hk' : k ∈ stabilizer (alternatingGroup α) s by
          simpa [mem_stabilizer_iff] using hk'
        apply MulAction.fixingSubgroup_le_stabilizer; exact hk
        exact k.prop
    · -- ∃ (k : fixing_subgroup (alternating_group α) s), k • b = x,
      haveI : IsPretransitive (fixingSubgroup (alternatingGroup α) s)
          (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) :=
        isPretransitive_ofFixingSubgroup s h0 hα
      obtain ⟨k, hk⟩ :=
        exists_smul_eq (fixingSubgroup (alternatingGroup α) s)
          (⟨b, hb'⟩ : SubMulAction.ofFixingSubgroup (alternatingGroup α) s) ⟨x, hx'⟩
      use k
      rw [← Subtype.coe_inj, SubMulAction.val_smul] at hk
      exact hk
  -- Conclusion of the proof : B = ⊤
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, hb⟩ := h1.nonempty
  obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x
  suffices g • B = B by
    rw [← hgbx, ← this, Set.smul_mem_smul_set_iff]
    exact hsc_le_B hb
  -- g • B = B,
  apply or_iff_not_imp_right.mp (IsBlock.def_one.mp hB ⟨g, hg⟩)
  rw [Set.not_disjoint_iff_nonempty_inter]
  change (g • B ∩ B).Nonempty
  apply Set.ncard_pigeonhole
  -- card B + card (g • B) = card B + card B
  -- ... ≥ card sᶜ + card sᶜ
  -- ... > card s + card s ᶜ = card α
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s]
  apply Nat.lt_of_lt_of_le
  · apply Nat.add_lt_add_right _ (Set.ncard (sᶜ : Set α))
    use Set.ncard (sᶜ : Set α)
    exact hα
  apply Nat.add_le_add
  · apply le_trans (Set.ncard_le_ncard hsc_le_B)
    apply le_of_eq
    rw [MulAction.smul_set_ncard_eq]
  exact Set.ncard_le_ncard hsc_le_B

theorem isMaximalStab'
    -- (hα : 4 < fintype.card α)
    (s : Set α)
    (h0' : s.Nontrivial) (h1' : sᶜ.Nontrivial) (hs : Set.ncard s < Set.ncard (sᶜ : Set α)) :
    Subgroup.IsMaximal (stabilizer (alternatingGroup α) s) := by
  suffices hα : 4 < Fintype.card α by
  -- h0 : s.nonempty, h1  : sᶜ.nonempty
  /-   have h1' : sᶜ.nontrivial,
    { rw [← set.nontrivial_coe, ← fintype.one_lt_card_iff_nontrivial],
      apply lt_of_le_of_lt _ hs,
      rw [nat.succ_le_iff, fintype.card_pos_iff, set.nonempty_coe_sort],
      exact h0, },
   -/
  --  cases em(s.nontrivial) with h0' h0',
  -- We start with the case where s.nontrivial
    constructor; constructor
    · -- stabilizer (alternating_group α) s ≠ ⊤
      exact stabilizer_ne_top' s h0'.nonempty h1'
    · -- ∀ (G : subgroup (alternating_group α)), stabilizer (alternating_group α) s < b) → b = ⊤
      intro G' hG'
      suffices alternatingGroup α ≤ G'.map (alternatingGroup α).subtype by
        rw [eq_top_iff]; intro g _
        obtain ⟨g', hg', hgg'⟩ := this g.prop
        simp only [Subgroup.coeSubtype, SetLike.coe_eq_coe] at hgg'
        rw [← hgg']; exact hg'
      --   apply is_maximal_stab'_temp' s hα,
      apply le_of_isPreprimitive s hα
      · rw [← Subgroup.subgroupOf_map_subtype, Subgroup.map_subtype_le_map_subtype]
        rw [MulAction.stabilizer_subgroupOf_eq] at hG'
        exact le_of_lt hG'
      · apply isPreprimitive_of_stabilizer_lt s h0' h1' hs (le_of_lt hα)
        rw [lt_iff_le_not_le]
        constructor
        · intro g
          simp only [Subgroup.mem_inf]
          rintro ⟨hg, hg'⟩
          refine And.intro ?_ hg'
          simp only [Subgroup.mem_map, Subgroup.coeSubtype, exists_prop]
          use ⟨g, hg'⟩
          constructor
          · apply le_of_lt hG'
            simpa only [mem_stabilizer_iff] using hg
          · rfl
        · intro h
          rw [lt_iff_le_not_le] at hG' ; apply hG'.right
          intro g' hg'
          rw [mem_stabilizer_iff]
          change (g' : Equiv.Perm α) • s = s; rw [← mem_stabilizer_iff]
          apply @inf_le_left (Subgroup (Equiv.Perm α)) _; apply h
          rw [Subgroup.mem_inf]
          apply And.intro _ g'.prop
          simp only [Subgroup.mem_map, Subgroup.coeSubtype, SetLike.coe_eq_coe, exists_prop, exists_eq_right]
          exact hg'
  -- hα : 4 < fintype.card α
  have h0 : 2 ≤ Set.ncard s := by
    rw [Nat.succ_le_iff, Set.one_lt_ncard_iff_nontrivial]
    exact h0'
  rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s]
  change 2 + 2 < _
  apply lt_of_le_of_lt
  exact Nat.add_le_add_right h0 2
  apply Nat.add_lt_add_left
  exact lt_of_le_of_lt h0 hs

theorem three_le {c n : ℕ} (h : 1 ≤ n) (h' : n < c) (hh' : c ≠ 2 * n) : 3 ≤ c :=
  by
  cases' Nat.eq_or_lt_of_le h with h h
  · rw [← h] at h' hh'
    cases' Nat.eq_or_lt_of_le h' with h' h'
    · exfalso; apply hh' h'.symm
    exact h'
  rw [Nat.succ_le_iff]
  exact lt_of_le_of_lt h h'

/-- stabilizer (alternating_group α) s is a maximal subgroup of alternating_group α,
  provided s ≠ ⊥, s ≠ ⊤ and fintype.card α ≠ 2 * fintype.card ↥s) -/
theorem Stabilizer.isMaximal (s : Set α) (h0 : s.Nonempty) (h1 : sᶜ.Nonempty)
    (hs : Fintype.card α ≠ 2 * Set.ncard s) :
    Subgroup.IsMaximal (stabilizer (alternatingGroup α) s) := by
  have hα : 3 ≤ Fintype.card α := by
    rw [← Set.ncard_pos, ← Nat.succ_le_iff] at h0 h1
    refine three_le h0 ?_ hs
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s]
    exact Nat.lt_add_of_pos_right h1
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    apply lt_of_lt_of_le _ hα
    norm_num
  have h : ∀ (t : Set α) (_ : t.Nonempty) (_ : t.Subsingleton),
    (stabilizer (alternatingGroup α) t).IsMaximal := by
    intro t ht ht'
    suffices ∃ a : α, t = ({a} : Set α) by
      obtain ⟨a, rfl⟩ := this
      have : stabilizer (alternatingGroup α) ({a} : Set α) = stabilizer (alternatingGroup α) a := by
        ext
        simp only [mem_stabilizer_iff, Set.smul_set_singleton, Set.singleton_eq_singleton_iff]
      rw [this]
      apply hasMaximalStabilizersOfPreprimitive
      apply AlternatingGroup.isPreprimitive hα
    · obtain ⟨a, ha⟩ := ht
      use a; exact Set.Subsingleton.eq_singleton_of_mem ht' ha
  by_cases h0' : Set.Nontrivial s
  -- cases' em s.Nontrivial with h0' h0'
  by_cases h1' : Set.Nontrivial sᶜ
  -- cases' em sᶜ.Nontrivial with h1' h1'
  -- h0' : s.nontrivial, h1' : sᶜ.nontrivial
  cases' Nat.lt_trichotomy (Set.ncard s) (Set.ncard (sᶜ : Set α)) with hs' hs'
  · exact isMaximalStab' s h0' h1' hs'
  cases' hs' with hs' hs'
  · exfalso; apply hs
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_add_ncard_compl s, ← hs', ← two_mul]
  · rw [← compl_compl s] at h0'
    rw [← stabilizer_compl]
    apply isMaximalStab' (sᶜ) h1' h0'
    simp_rw [compl_compl s]
    convert hs'
  -- h0' : s.nontrivial, h1' : ¬(s.nontrivial)
  · simp only [Set.not_nontrivial_iff] at h1'
    rw [← stabilizer_compl]
    exact h (sᶜ) h1 h1'
  -- h0' : ¬(s.nontrivial),
  · simp only [Set.not_nontrivial_iff] at h0'
    exact h s h0 h0'

/-- The action of alternating_group α on the n-element subsets of α is preprimitive
provided 0 < n < #α and #α ≠ 2*n -/
theorem Nat.Combination.isPreprimitive_of_alt (n : ℕ) (h_one_le : 1 ≤ n)
    (hn : n < Fintype.card α) (hα : Fintype.card α ≠ 2 * n) :
    IsPreprimitive (alternatingGroup α) (n.Combination α) := by
  have hα' : 3 ≤ Fintype.card α := three_le h_one_le hn hα
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial];
    exact lt_of_le_of_lt h_one_le hn
  cases' Nat.eq_or_lt_of_le h_one_le with h_one h_one_lt
  · -- n = 1 :
    rw [← h_one]
    apply isPreprimitive_of_surjective_map
      (Nat.bijective_toCombination_one_equivariant _ α).surjective
    exact AlternatingGroup.isPreprimitive hα'
  -- h_one_lt : 1 < n
  have ht : IsPretransitive (alternatingGroup α) (n.Combination α) := by
    -- apply nat.finset_is_pretransitive_of_multiply_pretransitive,
    have : Fintype.card α - n + n = Fintype.card α := by apply Nat.sub_add_cancel; exact le_of_lt hn
    rw [isPretransitive.of_bijective_map_iff Function.surjective_id
        (Nat.Combination_compl_bijective (alternatingGroup α) α this)]
    apply Nat.Combination_isPretransitive_of_IsMultiplyPretransitive
    apply isMultiplyPretransitive_of_higher (alternatingGroup α) α _
      (Nat.sub_le_sub_left h_one_lt _)
    · rw [ENat.card_eq_coe_fintype_card]
      simp only [ENat.coe_le_coe, tsub_le_self]
    · apply IsMultiplyPretransitive.alternatingGroup_of_sub_two
  have : Nontrivial (n.Combination α) :=
    Nat.Combination_nontrivial α (lt_trans (Nat.lt_succ_self 0) h_one_lt) hn
  obtain ⟨sn⟩ := Nontrivial.to_nonempty (α := n.Combination α)
  let s := sn.val
  let hs : s.card = n := sn.prop
  -- have hs : (s : finset α).card = n := s.prop,
  rw [← maximal_stabilizer_iff_preprimitive (alternatingGroup α) sn]
  have : stabilizer (alternatingGroup α) sn =
    stabilizer (alternatingGroup α) (s : Set α) := by
    ext g
    simp only [mem_stabilizer_iff]
    rw [← Subtype.coe_inj]
    change g • s = s ↔ _
    rw [← Finset.coe_smul_finset, ← Finset.coe_inj]
  rw [this]
  apply Stabilizer.isMaximal (s : Set α)
  · simp only [Finset.coe_nonempty, ← Finset.card_pos, hs]
    apply lt_trans one_pos h_one_lt
  · simp only [← Finset.coe_compl, Finset.coe_nonempty, ← Finset.card_compl_lt_iff_nonempty,
      compl_compl, hs]
    exact hn
  · simp only [Set.ncard_coe_Finset, hs]
    exact hα

end alternatingGroup


section Junk

variable {α G H : Type _} [Group G] [Group H] [MulAction G α] {N : Subgroup G}

theorem Subgroup.map_subgroupOf_eq {K : Subgroup N} : (K.map N.subtype).subgroupOf N = K := by
  rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]

theorem MulAction.stabilizer_subgroupOf_eq {a : α} :
    stabilizer N a = (stabilizer G a).subgroupOf N :=
  by
  ext n
  simp only [Subgroup.mem_subgroupOf, mem_stabilizer_iff]
  rfl

example (K K' : Subgroup G) : K < K' ↔ K ≤ K' ∧ K ≠ K' :=
  lt_iff_le_and_ne

theorem Subgroup.map_iff_mono_of_injective {f : G →* H} {K K' : Subgroup G}
    (hf : Function.Injective f) : K ≤ K' ↔ Subgroup.map f K ≤ Subgroup.map f K' :=
  by
  constructor
  exact Subgroup.map_mono
  · intro h
    intro x hx
    suffices f x ∈ Subgroup.map f K' by
      simp only [Subgroup.mem_map] at this
      obtain ⟨y, hy, hx⟩ := this
      rw [← hf hx]; exact hy
    apply h
    rw [Subgroup.mem_map]
    exact ⟨x, hx, rfl⟩

theorem Subgroup.map_strict_mono_of_injective {f : G →* H} {K K' : Subgroup G}
    (hf : Function.Injective f) :
    K < K' ↔ Subgroup.map f K < Subgroup.map f K' := by
  simp only [lt_iff_le_not_le]
  simp_rw [← Subgroup.map_iff_mono_of_injective hf]

theorem Subgroup.map_injective_of_injective {f : G →* H} {K K' : Subgroup G}
    (hf : Function.Injective f) :
    Subgroup.map f K = Subgroup.map f K' ↔ K = K' := by
  simp only [le_antisymm_iff, ← Subgroup.map_iff_mono_of_injective hf]

end Junk


