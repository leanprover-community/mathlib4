/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Perm.MaximalSubgroups
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Maximal subgroups of the alternating group

* `AlternatingGroup.isCoatom_stabilizer`: if neither `s : Set α` nor its complement is empty,
and if, moreover, `Nat.card α ≠ 2 * s.ncard',
then `stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternatingGroup α`.

This is the “intransitive case” of the O'Nan-Scott classification
of maximal subgroups of the alternating groups.

Compare with `Equiv.Perm.isCoatom_stabilizer` for the case of the permutation group.

## TODO

  * Application to primitivity of the action
    of `alternatingGroup α` on finite combinations of `α`.

  * Formalize the other cases of the classification.
    The next one should be the *imprimitive case*.

## Reference

The argument is taken from [M. Liebeck, C. Praeger, J. Saxl,
*A classification of the maximal subgroups of the finite
alternating and symmetric groups*, 1987][LiebeckPraegerSaxl-1987].

-/

open scoped Pointwise

open Equiv.Perm Equiv Set MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Equiv.Perm

theorem exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard
    {s : Set α} (hs : 2 < ncard s) :
    ∃ g ∈ stabilizer (Perm α) s,  g.IsThreeCycle := by
  rw [two_lt_ncard_iff] at hs
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hs
  use swap a b * swap a c
  refine ⟨?_, isThreeCycle_swap_mul_swap_same hab hac hbc⟩
  rw [← stabilizer_compl]
  rw [mem_stabilizer_set_iff_subset_smul_set sᶜ.toFinite, subset_smul_set_iff]
  rintro _ ⟨x, hx, rfl⟩
  simp only [mul_inv_rev, swap_inv, Perm.smul_def, Perm.coe_mul,
    Function.comp_apply, mem_compl_iff]
  rw [mem_compl_iff] at hx
  suffices h : ∀ u ∈ s, x ≠ u by
    rw [swap_apply_of_ne_of_ne (h a ha) (h b hb), swap_apply_of_ne_of_ne (h a ha) (h c hc)]
    exact hx
  grind  -- since x ∉ s, x ≠ u, for any u ∈ s

theorem exists_mem_stabilizer_isThreeCycle
    (s : Set α) (hα : 4 < Nat.card α) :
    ∃ g ∈ stabilizer (Perm α) s, g.IsThreeCycle := by
  rcases Nat.lt_or_ge 2 (ncard s) with hs | hs
  · exact exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard hs
  · suffices hs' : 2 < sᶜ.ncard by
      obtain ⟨g, hg, hg'⟩ := exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard hs'
      use g
      rw [stabilizer_compl] at hg
      exact ⟨hg, hg'⟩
    rw [lt_iff_not_ge] at hα ⊢
    intro hs'
    apply hα
    rw [← ncard_add_ncard_compl s]
    grind

theorem alternatingGroup_le_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (Perm α)) [hG' : IsPreprimitive G α] {s : Set α}
    (hG : stabilizer (Perm α) s ⊓ alternatingGroup α ≤ G) :
    alternatingGroup α ≤ G := by
  -- We need to prove that alternating_group α ≤ ⊤
  -- G contains a three_cycle
  obtain ⟨g, hg, hg3⟩ := exists_mem_stabilizer_isThreeCycle s h4
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG' hg3
  apply hG
  simp only [Subgroup.mem_inf, hg, true_and]
  exact IsThreeCycle.mem_alternatingGroup hg3

end Equiv.Perm

namespace AlternatingGroup

theorem stabilizer.surjective_toPerm {s : Set α} (hs : (sᶜ : Set α).Nontrivial) :
    Function.Surjective (toPerm : stabilizer (alternatingGroup α) s → Perm s) := by
  classical
  suffices ∃ k : Perm (sᶜ : Set α), sign k = -1 by
    obtain ⟨k, hk_sign⟩ := this
    have hks : ofSubtype k • s = s := by
      rw [← mem_stabilizer_iff, mem_stabilizer_set_iff_subset_smul_set s.toFinite]
      intro x hx
      exact ⟨x, hx, by simp [ofSubtype_apply_of_not_mem k (notMem_compl_iff.mpr hx)]⟩
    have hminus_one_ne_one : (-1 : Units ℤ) ≠ 1 := Ne.symm (units_ne_neg_self 1)
    intro g
    let g' := if sign g = 1
      then ofSubtype g
      else ofSubtype g * ofSubtype k
    use! g'
    · rw [mem_alternatingGroup]
      rcases Int.units_eq_one_or (sign g) with hsg | hsg <;>
      · simp only [g', if_true, hminus_one_ne_one, if_false, sign_ofSubtype,
        sign_mul, mul_neg, mul_one, neg_neg, hsg, hk_sign]
    · rw [mem_stabilizer_iff, Submonoid.mk_smul]
      rcases Int.units_eq_one_or (sign g) with hsg | hsg
      · simp only [g', hsg, if_true]
        exact ofSubtype_mem_stabilizer g
      · simp only [g', hsg, hminus_one_ne_one, if_false, mul_smul, hks]
        exact ofSubtype_mem_stabilizer g
    · dsimp only [id_eq, ite_true, ite_false, eq_mpr_eq_cast, cast_eq]
      rcases Int.units_eq_one_or (sign g) with hsg | hsg
      · simp only [g', hsg, if_true]
        ext x
        simp
      · simp only [g', hsg, hminus_one_ne_one, if_false]
        ext x
        simp only [toPerm_apply, SMul.smul_stabilizer_def]
        simp only [Subgroup.mk_smul, Perm.smul_def, coe_mul, Function.comp_apply]
        rw [ofSubtype_apply_of_not_mem k _]
        · exact ofSubtype_apply_coe g x
        · rw [notMem_compl_iff]; exact x.prop
  -- ∃ k : equiv.perm (sᶜ : set α), equiv.perm.sign k = -1,
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  use Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩
  rw [sign_swap _]
  simp [← Function.Injective.ne_iff Subtype.coe_injective, hab]

theorem stabilizer.isPreprimitive {s : Set α} (hs : (sᶜ : Set α).Nontrivial) :
    IsPreprimitive (stabilizer (alternatingGroup α) s) s := by
  classical
  let φ : stabilizer (alternatingGroup α) s → Perm s := MulAction.toPerm
  let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' _ _ := rfl }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_congr (stabilizer.surjective_toPerm hs) hf]
  infer_instance

theorem stabilizer.isPreprimitive' {s : Set α} (hsc : sᶜ.Nontrivial)
    {G : Subgroup (alternatingGroup α)} (hG : stabilizer (alternatingGroup α) s ≤ G) :
    IsPreprimitive (stabilizer G s) s :=
  have := stabilizer.isPreprimitive hsc
  let φ (g : stabilizer (alternatingGroup α) s) : stabilizer G s := ⟨⟨g, hG g.prop⟩, g.prop⟩
  let f : s →ₑ[φ] s :=
    { toFun := id
      map_smul' _ _ := rfl }
  IsPreprimitive.of_surjective (f := f) Function.surjective_id

/-- If `s : Set α` is nonempty and its complement has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
theorem stabilizer_ne_top {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  rw [mem_compl_iff] at hb hc
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
    rw [← swap_isSwap_iff] at hab hac
    exact swap_mul_swap_mem_alternatingGroup hab hac
  rw [← Subgroup.mk_smul g hg, ← MulAction.mem_stabilizer_iff, h]
  apply Subgroup.mem_top

end AlternatingGroup

namespace MulAction.IsBlock

open AlternatingGroup

theorem subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le
    {s B : Set α} {G : Subgroup (alternatingGroup α)}
    (hs : s.Nontrivial) (hB_ss_sc : B ⊂ sᶜ) (hG : stabilizer (alternatingGroup α) s ≤ G)
    (hB : IsBlock G B) :
    B.Subsingleton := by
  rw [← inter_eq_self_of_subset_right (subset_of_ssubset hB_ss_sc), ← Subtype.image_preimage_val]
  apply Subsingleton.image
  suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)) by
    apply Or.resolve_right this
    intro hB'
    apply ne_of_lt hB_ss_sc
    apply subset_antisymm (by grind)
    simpa only [preimage_eq_univ_iff, Subtype.range_coe_subtype] using hB'
  suffices IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α) by
    apply this.isTrivialBlock_of_isBlock
    let φ' : stabilizer G (sᶜ : Set α) → G := Subtype.val
    let f' : (sᶜ : Set α) →ₑ[φ'] α := {
      toFun := Subtype.val
      map_smul' := fun m x => by simp only [φ', SMul.smul_stabilizer_def] }
    exact hB.preimage f'
  apply stabilizer.isPreprimitive'
  · rwa [compl_compl]
  · rwa [stabilizer_compl]

theorem subsingleton_of_stabilizer_alternatingGroup_lt_of_subset
    {s B : Set α} {G : Subgroup (alternatingGroup α)}
    (hB_not_le_sc : ∀ (B : Set α), IsBlock G B → B ⊆ sᶜ → B.Subsingleton)
    (hs : sᶜ.Nontrivial) (hG : stabilizer (alternatingGroup α) s < G)
    (hBs : B ≤ s) (hB : IsBlock G B) :
    B.Subsingleton := by
  suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
    rcases this with hB' | hB'
    · rw [← inter_eq_self_of_subset_right hBs, ← Subtype.image_preimage_val]
      apply hB'.image
    · have hBs' : B = s := by
        apply antisymm hBs
        intro x hx
        rw [show x = Subtype.val (⟨x, hx⟩ : s) from by simp, ← mem_preimage, hB']
        apply mem_univ
      have : ∃ g' ∈ G, g' • s ≠ s := by
        by_contra! h
        apply ne_of_lt hG
        exact le_antisymm (le_of_lt hG) h
      obtain ⟨g', hg', hg's⟩ := this
      rcases isBlock_iff_smul_eq_or_disjoint.mp hB ⟨g', hg'⟩ with h | h
      · -- case g' • B = B : absurd, since B = s and choice of g'
        exfalso
        apply hg's; rw [← hBs']; exact h
      · -- case g' • B disjoint from B
        suffices (g' • B).Subsingleton by
          apply subsingleton_of_image _ B this
          apply Function.Bijective.injective (MulAction.bijective _)
        apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B) (hB.translate _)
        rw [← hBs']
        exact Disjoint.subset_compl_right h
  suffices IsPreprimitive (stabilizer G s) (s : Set α) by
    apply this.isTrivialBlock_of_isBlock
    let φ' : stabilizer G s → G := Subtype.val
    let f' : s →ₑ[φ'] α := {
      toFun := Subtype.val
      map_smul' := fun ⟨m, _⟩ x => by simp [φ'] }
    exact hB.preimage f'
  exact stabilizer.isPreprimitive' hs (le_of_lt hG)

theorem compl_subset_of_stabilizer_alternatingGroup_le_of_not_subset_of_not_subset_compl
    {s B : Set α} {G : Subgroup (alternatingGroup α)} (hG : stabilizer (alternatingGroup α) s ≤ G)
    (hBs : ¬ B ⊆ s) (hBsc : ¬ B ⊆ sᶜ) (h : s.ncard + 1 ≤ Nat.card α - 2) (hB : IsBlock G B) :
    sᶜ ⊆ B := fun x hx' ↦ by
  have : ∃ a : α, a ∈ B ∧ a ∈ s := by grind
  obtain ⟨a, ha, ha'⟩ := this
  have : ∃ b : α, b ∈ B ∧ b ∈ sᶜ := by grind
  obtain ⟨b, hb, hb'⟩ := this
  suffices ∃ k : fixingSubgroup (alternatingGroup α) s, k • b = x by
    obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
    suffices k • B = B by
      rw [← hkbx, ← this, smul_mem_smul_set_iff]
      exact hb
    suffices hk_mem : k ∈ G by
      apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨k, hk_mem⟩)
      simp only [Subgroup.mk_smul]
      use a
      refine ⟨?_, ha⟩
      rw [mem_fixingSubgroup_iff] at hk
      rw [← hk a ha']
      exact smul_mem_smul_set ha
    exact hG (fixingSubgroup_le_stabilizer (↥(alternatingGroup α)) s hk)
  · -- ∃ (k : fixingSubgroup (alternatingGroup α) s), k • b = x,
    suffices IsPretransitive (fixingSubgroup (alternatingGroup α) s)
        (SubMulAction.ofFixingSubgroup (alternatingGroup α) s) by
      obtain ⟨k, hk⟩ :=
        exists_smul_eq (fixingSubgroup (alternatingGroup α) s)
          (⟨b, hb'⟩ : SubMulAction.ofFixingSubgroup (alternatingGroup α) s) ⟨x, hx'⟩
      use k
      rw [← Subtype.coe_inj, SubMulAction.val_smul] at hk
      exact hk
    rw [← is_one_pretransitive_iff]
    suffices IsMultiplyPretransitive (alternatingGroup α) α (s.ncard + 1) by
      apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (alternatingGroup α) s rfl
    have : IsMultiplyPretransitive (alternatingGroup α) α (Nat.card α - 2) :=
      isMultiplyPretransitive α
    -- s.ncard + 1 ≤ Nat.card α - 2
    apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) h
    exact Nat.sub_le (Nat.card α) 2

end MulAction.IsBlock

namespace AlternatingGroup

/- Here, we needs either that `Nat.card α` has at least `4` elements,
so that  either `t` has at least 3 elements, or `tᶜ` has at least 2.
The condition is necessary, because the result is wrong when
`α = {1, 2, 3}` and either `t = {1, 2}` or `t = {1}`. -/
theorem moves_in (hα : 4 ≤ Nat.card α) {t : Set α} {a b : α}
    (ha : a ∈ t) (hb : b ∈ t) :
    ∃ g ∈ stabilizer (alternatingGroup α) t, g • a = b := by
  by_cases hab : a = b
  · -- a = b, we take g = 1,
    use 1
    simp only [hab, Subgroup.one_mem, one_smul, and_self]
  -- `a ≠ b`
  rcases le_or_gt (ncard t) 2 with ht | ht'
  · -- If `ncard t ≤ 2`, then we take the product of `swap a b` with a swap in `tᶜ`.
    have h : 1 < ncard (tᶜ : Set α) := by
      rw [← not_lt, ← ncard_add_ncard_compl t] at hα
      grind
    rw [one_lt_ncard_iff] at h
    obtain ⟨c, d, hc, hd, hcd⟩ := h
    use ⟨Equiv.swap a b * Equiv.swap c d, by
      apply swap_mul_swap_mem_alternatingGroup <;> rwa [swap_isSwap_iff]⟩
    constructor
    · rw [mem_stabilizer_set_iff_subset_smul_set t.toFinite, subset_smul_set_iff]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Subgroup.smul_def, Subgroup.coe_inv, mul_inv_rev, Perm.smul_def, swap_inv,
        Perm.coe_mul, Function.comp_apply]
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
    · simp only [Subgroup.smul_def, Perm.smul_def, Perm.coe_mul, Function.comp_apply]
      rw [mem_compl_iff t] at hc hd
      have hac : a ≠ c := by intro h; apply hc; rw [← h]; exact ha
      have had : a ≠ d := by intro h; apply hd; rw [← h]; exact ha
      rw [swap_apply_of_ne_of_ne hac had, swap_apply_left]
  · -- If `card t ≥ 3`, then there is a 3-cycle with support in `t`
    suffices ∃ c ∈ t, c ≠ a ∧ c ≠ b by
      obtain ⟨c, hc, hca, hcb⟩ := this
      use ⟨swap a c * swap a b, by
          apply swap_mul_swap_mem_alternatingGroup <;> rw [swap_isSwap_iff]
          · exact hca.symm
          · exact hab⟩
      constructor
      · rw [mem_stabilizer_set_iff_subset_smul_set t.toFinite, subset_smul_set_iff]
        simp only [Subgroup.smul_def, Subgroup.coe_inv, mul_inv_rev, swap_inv]
        suffices ∀ (a b) (ha : a ∈ t) (hb : b ∈ t), swap a b • t ⊆ t by
          rw [mul_smul]
          apply subset_trans _ (this a b ha hb)
          exact smul_set_mono (this a c ha hc)
        rintro a b ha hb _ ⟨x, hx, rfl⟩
        simp only [Perm.smul_def]
        by_cases hxa : x = a
        · simpa [hxa]
        by_cases hxb : x = b
        · simpa [hxb]
        simpa [swap_apply_of_ne_of_ne hxa hxb]
      · simp only [Subgroup.smul_def, Perm.smul_def, Perm.coe_mul, Function.comp_apply,
          swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
    suffices (t \ {a, b}).Nonempty by
      obtain ⟨c, h⟩ := this
      simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or] at h
      use c
    apply Set.diff_nonempty_of_ncard_lt_ncard (hs := toFinite _)
    rwa [ncard_pair hab]

theorem subgroup_eq_top_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (alternatingGroup α)) [hG' : IsPreprimitive G α] {s : Set α}
    (hG : stabilizer (alternatingGroup α) s ≤ G) :
    G = ⊤ := by
  obtain ⟨g, hg, hg3⟩ := exists_mem_stabilizer_isThreeCycle s h4
  suffices alternatingGroup α ≤ G.map (Subgroup.subtype _) by
    rw [Subgroup.eq_top_iff']
    intro x
    simpa using this x.prop
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem  _ hg3
  · lift g to alternatingGroup α using hg3.mem_alternatingGroup
    use g
    simpa only [SetLike.mem_coe, Subgroup.subtype_apply, and_true] using hG hg
  · let φ : G → Subgroup.map (alternatingGroup α).subtype G := fun g ↦ ⟨g, by simp⟩
    let f : α →ₑ[φ] α := {
      toFun := id
      map_smul' g a := rfl  }
    rwa [← isPreprimitive_congr (φ := φ) (f:= f) ?_ Function.bijective_id]
    · rintro ⟨_, ⟨g, hg⟩, hg', rfl⟩
      exact ⟨⟨⟨g, hg⟩, hg'⟩, rfl⟩

theorem isPreprimitive_of_stabilizer_lt (h4 : 4 ≤ Nat.card α)
    {s : Set α} (h0 : s.Nontrivial) (hs : ncard s < ncard sᶜ)
    {G : Subgroup (alternatingGroup α)} (hG : stabilizer (alternatingGroup α) s < G) :
    IsPreprimitive G α := by

  have h1 : sᶜ.Nontrivial := by
    rw [← not_subsingleton_iff, ← ncard_le_one_iff_subsingleton, not_le]
    apply lt_of_le_of_lt _ hs
    exact h0.nonempty.ncard_pos

  -- G acts transitively
  have : IsPretransitive G α := by
    have hG' : stabilizer (alternatingGroup α) s ≤ G := le_of_lt hG
    apply IsPretransitive.of_partition G (s := s)
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := moves_in h4 ha hb
      use! ⟨g, hG' hg⟩, H
    · intro a ha b hb
      obtain ⟨g, hg, H⟩ := moves_in h4 ha hb
      use! g, hG' (by rwa [stabilizer_compl] at hg), H
    · intro h
      apply (lt_iff_le_not_ge.mp hG).right
      intro g hg
      simp only [mem_stabilizer_iff]
      rw [← Subgroup.coe_mk G g hg, ← Subgroup.smul_def, ← mem_stabilizer_iff, h]
      exact Subgroup.mem_top _

  apply IsPreprimitive.mk
  -- We reduce to proving that a block which is not a subsingleton is `univ`.
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'

  -- The proof needs 4 steps
  /- Step 1 : `sᶜ` is not a block.
       This uses that `s.ncard  < sᶜ.ncard`.
       In the equality case, it is possible that `B = sᶜ` is a block:
       in that case, `G` would be a wreath product,
       this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the alternating group. -/
  have not_isBlock_sc : ¬ IsBlock G sᶜ := fun hsc ↦ by
    apply compl_ne_univ.mpr h0.nonempty -- `sᶜ ≠ univ`
    apply hsc.eq_univ_of_card_lt
    rw [← ncard_add_ncard_compl s, mul_two]
    simpa only [add_lt_add_iff_right]

  -- Step 2 : A block contained in `sᶜ` is a subsingleton
  have hB_not_le_sc (B : Set α) (hB : IsBlock G B) (hBsc : B ⊆ sᶜ) :
      B.Subsingleton :=
    IsBlock.subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le h0
      (HasSubset.Subset.ssubset_of_ne hBsc (by aesop)) -- uses Step 1
      (le_of_lt hG) hB

 -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s (B : Set α) (hB : IsBlock G B) (hBs : B ⊆ s) :
      B.Subsingleton :=
    IsBlock.subsingleton_of_stabilizer_alternatingGroup_lt_of_subset hB_not_le_sc h1 hG hBs hB

  -- Step 4 : sᶜ ⊆ B : A block which is not a subsingleton contains `sᶜ`.
  have hsc_le_B : sᶜ ⊆ B := by
    apply IsBlock.compl_subset_of_stabilizer_alternatingGroup_le_of_not_subset_of_not_subset_compl
      (le_of_lt hG) (fun a ↦ hB' (hB_not_le_s B hB a)) (fun a ↦ hB' (hB_not_le_sc B hB a)) _ hB
    apply Nat.le_sub_of_add_le
    simp only [add_assoc, ← ncard_add_ncard_compl s, Nat.reduceAdd,
      add_le_add_iff_left, Nat.succ_le_iff]
    apply lt_of_le_of_lt _ hs
    rwa [Nat.succ_le_iff, one_lt_ncard]

  -- Conclusion of the proof : `B = univ`
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨b, hb⟩ := h1.nonempty
  obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x
  suffices g • B = B by
    rw [← hgbx, ← this, smul_mem_smul_set_iff]
    exact hsc_le_B hb
  -- g • B = B,
  apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨g, hg⟩)
  simp only [Subgroup.mk_smul]
  apply nonempty_inter_of_lt_ncard_add_ncard
  calc Nat.card α = s.ncard + sᶜ.ncard := by rw [Set.ncard_add_ncard_compl]
      _ < sᶜ.ncard + sᶜ.ncard := by rwa [Nat.add_lt_add_iff_right]
      _ = 2 * sᶜ.ncard := by rw [two_mul]
      _ ≤ 2 * B.ncard := by have := Set.ncard_le_ncard hsc_le_B; gcongr
      _ = _ := by simp only [Set.ncard_smul_set, ← two_mul]

theorem isCoatom_stabilizer_of_ncard_lt_ncard_compl {s : Set α}
    (h0' : s.Nontrivial) (hs : s.ncard < (sᶜ : Set α).ncard) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have h1' : sᶜ.Nontrivial := by
    rw [← not_subsingleton_iff, ← ncard_le_one_iff_subsingleton, not_le]
    apply lt_of_le_of_lt _ hs
    exact h0'.nonempty.ncard_pos
  suffices hα : 4 < Nat.card α by
  -- We start with the case where s is nontrivial
    constructor
    · -- stabilizer (alternating_group α) s ≠ ⊤
      apply stabilizer_ne_top h0'.nonempty h1'
    · -- ∀ (G : subgroup (alternating_group α)), stabilizer (alternating_group α) s < b) → b = ⊤
      intro G hG
      have : IsPreprimitive G α :=
        isPreprimitive_of_stabilizer_lt (Nat.le_of_add_left_le hα) h0' hs hG
      apply subgroup_eq_top_of_isPreprimitive hα (s := s) (hG := le_of_lt hG)
  -- `4 < Nat.card α`
  rw [Set.Nontrivial, ← one_lt_ncard] at h0' h1'
  rw [← ncard_add_ncard_compl s]
  grind

theorem isCoatom_stabilizer_singleton (h3 : 3 ≤ Nat.card α)
    {s : Set α} (h : s.Nonempty) (h1 : s.Subsingleton) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have : Nontrivial α := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card]
    grind
  obtain ⟨a, ha⟩ := h
  rw [Subsingleton.eq_singleton_of_mem h1 ha, stabilizer_singleton]
  have : IsPreprimitive (alternatingGroup α) α :=
    AlternatingGroup.isPreprimitive_of_three_le_card α h3
  apply IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive

/-- `stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternatingGroup α`,
provided `s ≠ ∅`, `sᶜ ≠ ∅` and `Nat.card α ≠ 2 * s.ncard`.

This is the intransitive case of the O'Nan–Scott classification. -/
theorem isCoatom_stabilizer {s : Set α}
    (h0 : s.Nonempty) (h1 : sᶜ.Nonempty) (hs : Nat.card α ≠ 2 * ncard s) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  rw [← ncard_add_ncard_compl s, two_mul, ne_eq, Nat.add_left_cancel_iff] at hs
  wlog hs' : ncard s < ncard sᶜ
  · rw [← stabilizer_compl]
    apply this h1 (by rwa [compl_compl]) _
    · rw [compl_compl, ← not_le]
      grind
    · simp only [compl_compl]
      grind
  · by_cases h0' : s.Nontrivial
    · apply isCoatom_stabilizer_of_ncard_lt_ncard_compl h0' hs'
    · simp only [not_nontrivial_iff] at h0'
      apply isCoatom_stabilizer_singleton _ h0 h0'
      rw [← ncard_add_ncard_compl s] at ⊢
      rw [← ncard_pos, ← Nat.succ_le_iff] at h0 h1
      grind

end AlternatingGroup
