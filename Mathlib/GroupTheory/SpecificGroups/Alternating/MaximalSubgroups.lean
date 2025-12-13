/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Perm.MaximalSubgroups
public import Mathlib.GroupTheory.SpecificGroups.Alternating

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

@[expose] public section

open scoped Pointwise

open Equiv.Perm Equiv Set MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Equiv.Perm

theorem exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard
    {s : Set α} (hs : 2 < ncard s) :
    ∃ g ∈ stabilizer (Perm α) s, g.IsThreeCycle := by
  rw [two_lt_ncard_iff] at hs
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hs
  use swap a b * swap a c
  refine ⟨?_, isThreeCycle_swap_mul_swap_same hab hac hbc⟩
  rw [mem_stabilizer_set_iff_subset_smul_set s.toFinite, subset_smul_set_iff]
  rintro _ ⟨x, hx, rfl⟩
  aesop

theorem exists_mem_stabilizer_isThreeCycle
    (s : Set α) (hα : 4 < Nat.card α) :
    ∃ g ∈ stabilizer (Perm α) s, g.IsThreeCycle := by
  rcases Nat.lt_or_ge 2 (ncard s) with hs | hs
  · exact exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard hs
  · have := ncard_add_ncard_compl s
    rw [← stabilizer_compl]
    exact exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard (by grind)

theorem alternatingGroup_le_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (Perm α)) [hG' : IsPreprimitive G α] {s : Set α}
    (hG : stabilizer (Perm α) s ⊓ alternatingGroup α ≤ G) :
    alternatingGroup α ≤ G := by
  -- G contains a three_cycle
  obtain ⟨g, hg, hg3⟩ := exists_mem_stabilizer_isThreeCycle s h4
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG' hg3
  exact hG ⟨hg, IsThreeCycle.mem_alternatingGroup hg3⟩

end Equiv.Perm

namespace AlternatingGroup

theorem stabilizer.surjective_toPerm {s : Set α} (hs : sᶜ.Nontrivial) :
    Function.Surjective (toPerm : stabilizer (alternatingGroup α) s → Perm s) := by
  classical
  suffices ∃ k : Perm (sᶜ : Set α), sign k = -1 by
    obtain ⟨k, hk_sign⟩ := this
    have hks : ofSubtype k • s = s := by
      rw [← mem_stabilizer_iff, mem_stabilizer_set_iff_subset_smul_set s.toFinite]
      intro x hx
      exact ⟨x, hx, by simp [ofSubtype_apply_of_not_mem k (notMem_compl_iff.mpr hx)]⟩
    intro g
    rcases Int.units_eq_one_or (sign g) with hsg | hsg
    · use! ofSubtype g
      · simp [mem_alternatingGroup, hsg]
      · rw [mem_stabilizer_iff, Submonoid.mk_smul]
        exact ofSubtype_mem_stabilizer g
      · aesop
    use! ofSubtype g * ofSubtype k
    · simp [mem_alternatingGroup, hk_sign, hsg]
    · rw [mem_stabilizer_iff, Submonoid.mk_smul, mul_smul, hks]
      exact ofSubtype_mem_stabilizer g
    · ext x
      simp [ofSubtype_apply_of_not_mem k]
  -- `∃ k : Equiv.Perm (sᶜ : Set α), Equiv.Perm.sign k = -1`,
  obtain ⟨a, ha, b, hb, hab⟩ := hs
  use Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩
  rw [sign_swap _]
  simp [← Function.Injective.ne_iff Subtype.coe_injective, hab]

/-- In the alternating group, the stabilizer of a set acts
primitively on that set if the complement is nontrivial. -/
theorem stabilizer_isPreprimitive {s : Set α} (hs : (sᶜ : Set α).Nontrivial) :
    IsPreprimitive (stabilizer (alternatingGroup α) s) s := by
  let φ : stabilizer (alternatingGroup α) s → Perm s := MulAction.toPerm
  let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' _ _ := rfl }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_congr (stabilizer.surjective_toPerm hs) hf]
  infer_instance

/-- A subgroup of the alternating group that contains
the stabilizer of a set acts primitively on that set
if the complement is nontrivial. -/
theorem stabilizer_subgroup_isPreprimitive {s : Set α} (hsc : sᶜ.Nontrivial)
    {G : Subgroup (alternatingGroup α)} (hG : stabilizer (alternatingGroup α) s ≤ G) :
    IsPreprimitive (stabilizer G s) s :=
  have := stabilizer_isPreprimitive hsc
  let φ (g : stabilizer (alternatingGroup α) s) : stabilizer G s :=
      ⟨⟨g, hG g.prop⟩, g.prop⟩
  let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' _ _ := rfl }
  IsPreprimitive.of_surjective (f := f) Function.surjective_id

/-- If `s : Set α` is nonempty and its complement has at least two elements,
then `stabilizer (alternatingGroup α) s ≠ ⊤`. -/
theorem stabilizer_ne_top {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nontrivial) :
    stabilizer (alternatingGroup α) s ≠ ⊤ := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb, c, hc, hbc⟩ := hsc
  suffices ∃ g, g ∉ stabilizer (alternatingGroup α) s by contrapose! this; simp [this]
  use ⟨Equiv.swap a b * Equiv.swap a c, by aesop⟩
  simp_rw [mem_stabilizer_set, Subgroup.mk_smul, mul_smul, Perm.smul_def]
  grind

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
  apply stabilizer_subgroup_isPreprimitive
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
    · have hBs' : B = s := by aesop
      have : ∃ g' ∈ G, g' • s ≠ s := by
        by_contra! h
        apply ne_of_lt hG
        exact le_antisymm (le_of_lt hG) h
      obtain ⟨g', hg', hg's⟩ := this
      rcases isBlock_iff_smul_eq_or_disjoint.mp hB ⟨g', hg'⟩ with h | h
      · -- case g' • B = B : absurd, since B = s and choice of g'
        simp_all
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
  exact stabilizer_subgroup_isPreprimitive hs (le_of_lt hG)

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

/- Here, we need that `Nat.card α` has at least `4` elements,
so that  either `t` has at least 3 elements, or `tᶜ` has at least 2.
The condition is necessary, because the result is wrong when
`α = {1, 2, 3}` and either `t = {1, 2}` or `t = {1}`. -/
theorem moves_in (hα : 4 ≤ Nat.card α) {t : Set α} {a b : α}
    (ha : a ∈ t) (hb : b ∈ t) :
    ∃ g ∈ stabilizer (alternatingGroup α) t, g • a = b := by
  by_cases hab : a = b
  · use 1
    simpa
  by_cases ht : 2 < t.ncard
  · rw [← Set.ncard_pair hab] at ht
    replace ht := Set.diff_nonempty_of_ncard_lt_ncard ht
    obtain ⟨c, hct, hc⟩ := ht
    simp only [mem_insert_iff, not_or] at hc
    refine ⟨⟨swap c a * swap a b, by simp [hab, hc.1]⟩, ?_, ?_⟩
    · simp only [mem_stabilizer_set' t.toFinite, Subgroup.mk_smul, Perm.smul_def, coe_mul]
      grind
    · simp only [Subgroup.mk_smul, Perm.smul_def, coe_mul]
      grind
  · have := ncard_add_ncard_compl t
    obtain ⟨c, d, hc, hd, hcd⟩ := (one_lt_ncard_iff tᶜ.toFinite).mp (by grind)
    refine ⟨⟨swap a b * swap c d, by simp [hab, hcd]⟩, ?_, ?_⟩
    · simp only [mem_stabilizer_set' t.toFinite, Subgroup.mk_smul, Perm.smul_def, coe_mul]
      grind
    · simp only [Subgroup.smul_def, Perm.smul_def, Perm.coe_mul]
      grind

theorem subgroup_eq_top_of_isPreprimitive (h4 : 4 < Nat.card α)
    (G : Subgroup (alternatingGroup α)) [hG' : IsPreprimitive G α] {s : Set α}
    (hG : stabilizer (alternatingGroup α) s ≤ G) :
    G = ⊤ := by
  obtain ⟨g, hg, hg3⟩ := exists_mem_stabilizer_isThreeCycle s h4
  rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- By Jordan's theorem, it suffices to prove that G acts primitively
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem  _ hg3
  · use ⟨g, hg3.mem_alternatingGroup⟩
    simpa only [SetLike.mem_coe, Subgroup.subtype_apply, and_true] using hG hg
  · let φ := (alternatingGroup α).subtype.subgroupMap G
    let f : α →ₑ[φ] α := {
      toFun := id
      map_smul' g a := rfl  }
    rwa [← isPreprimitive_congr (f := f) ((alternatingGroup α).subtype.subgroupMap_surjective G)
      Function.bijective_id]

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
      rwa [← Subgroup.subgroupOf_eq_top]
  apply IsPreprimitive.mk
  -- We reduce to proving that a block which is not a subsingleton is `univ`.
  intro B hB
  rw [IsTrivialBlock, or_iff_not_imp_left]
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
      _ ≤ 2 * B.ncard := by grw [Set.ncard_le_ncard hsc_le_B]
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
    · -- `stabilizer (alternatingGroup α) s ≠ ⊤`
      apply stabilizer_ne_top h0'.nonempty h1'
    · -- `∀ (G : Subgroup (alternatingGroup α)), stabilizer (alternatingGroup α) s < b) → b = ⊤`
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
