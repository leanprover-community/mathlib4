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

* `alternatingGroup.isCoatom_stabilizer`: if neither `s : Set α` nor its complement is empty,
  and if, moreover, `Nat.card α ≠ 2 * s.ncard`,
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

public section

open scoped Pointwise

open Equiv.Perm Equiv Set MulAction

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace Equiv.Perm

theorem exists_mem_stabilizer_isThreeCycle_of_two_lt_ncard
    {s : Set α} (hs : 2 < ncard s) :
    ∃ g ∈ stabilizer (Perm α) s, g.IsThreeCycle := by
  rw [two_lt_ncard_iff] at hs
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hs
  refine ⟨swap a b * swap a c, ?_, isThreeCycle_swap_mul_swap_same hab hac hbc⟩
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

namespace alternatingGroup

theorem stabilizer.surjective_toPerm {s : Set α} (hs : sᶜ.Nontrivial) :
    Function.Surjective (toPerm : stabilizer (alternatingGroup α) s → Perm s) := by
  classical
  have : ∃ k : Perm α, IsSwap k ∧ _root_.Disjoint s k.support := by
    obtain ⟨a, ha, b, hb, hab⟩ := hs
    use Equiv.swap a b
    rw [swap_isSwap_iff]; aesop
  obtain ⟨k, hk_swap, hk_support⟩ := this
  have hks : k • s = s := by
    rw [← mem_stabilizer_iff, mem_stabilizer_set_iff_smul_set_subset s.toFinite]
    intro _
    simp only [mem_smul_set]
    rintro ⟨x, hx, rfl⟩
    convert hx
    rw [Perm.smul_def, ← Perm.notMem_support]
    exact (Set.disjoint_left.mp hk_support) hx
  intro g
  rcases Int.units_eq_one_or (sign g) with hsg | hsg
  · use! ofSubtype g
    · simp [mem_alternatingGroup, hsg]
    · rw [mem_stabilizer_iff, Submonoid.mk_smul]
      exact ofSubtype_mem_stabilizer g
    · aesop
  · use! ofSubtype g * k
    · simp [mem_alternatingGroup, hk_swap.sign_eq, hsg]
    · rw [mem_stabilizer_iff, Submonoid.mk_smul, mul_smul, hks, ofSubtype_mem_stabilizer]
    · ext x
      suffices k x = x by simp [this]
      rw [Set.disjoint_left] at hk_support
      rw [← notMem_support]
      exact hk_support x.prop

/-- In the alternating group, the stabilizer of a set acts
primitively on that set if the complement is nontrivial. -/
theorem stabilizer_isPreprimitive {s : Set α} (hs : (sᶜ : Set α).Nontrivial) :
    IsPreprimitive (stabilizer (alternatingGroup α) s) s :=
  isPreprimitive_stabilizer_of_surjective s (stabilizer.surjective_toPerm hs)

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

/- Here, we need that `Nat.card α` has at least `4` elements,
so that  either `t` has at least 3 elements, or `tᶜ` has at least 2.
The condition is necessary, because the result is wrong when
`α = {1, 2, 3}` and either `t = {1, 2}` or `t = {1}`. -/
theorem exists_mem_stabilizer_smul_eq (hα : 4 ≤ Nat.card α) {t : Set α} :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g ∈ stabilizer (alternatingGroup α) t, g • a = b := by
  intro a ha b hb
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
  apply alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem _ hg3
  · use ⟨g, hg3.mem_alternatingGroup⟩
    simpa only [SetLike.mem_coe, Subgroup.subtype_apply, and_true] using hG hg
  · let φ := (alternatingGroup α).subtype.subgroupMap G
    let f : α →ₑ[φ] α := {
      toFun := id
      map_smul' _ _ := rfl }
    rwa [← isPreprimitive_congr (f := f) ((alternatingGroup α).subtype.subgroupMap_surjective G)
      Function.bijective_id]

end alternatingGroup

namespace MulAction.IsBlock

open alternatingGroup

theorem subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le
    {s B : Set α} {G : Subgroup (alternatingGroup α)}
    (hs : s.Nontrivial) (hB_ss_sc : B ⊂ sᶜ) (hG : stabilizer (alternatingGroup α) s ≤ G)
    (hB : IsBlock G B) :
    B.Subsingleton := by
  apply hB.subsingleton_of_ssubset_of_stabilizer_le hB_ss_sc
  intro g
  obtain ⟨⟨k, hk⟩, rfl⟩ := alternatingGroup.stabilizer.surjective_toPerm (by rwa [compl_compl]) g
  rw [stabilizer_compl] at hk
  exact ⟨⟨⟨k, hG hk⟩, by aesop⟩, rfl⟩

end MulAction.IsBlock

namespace alternatingGroup

/- Note : The proof of this statement is close to that
of `Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl`,
and while it would not be absolutely impossible to abstract both proofs,
the result would be slightly awkward because the
details of the results involved in the proof differ in annoying details.
And it would be used only twice. -/
theorem isCoatom_stabilizer_of_ncard_lt_ncard_compl {s : Set α}
    (h0 : s.Nontrivial) (hs : s.ncard < (sᶜ : Set α).ncard) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have := ncard_add_ncard_compl s
  have h1 : sᶜ.Nontrivial := by
    rw [← one_lt_ncard_iff_nontrivial]
    exact lt_of_le_of_lt h0.nonempty.ncard_pos hs
  have hα : 4 < Nat.card α := by
    rw [← Set.one_lt_ncard_iff_nontrivial] at h0
    grind
  -- To prove that `stabilizer (alternatingGroup α) s` is maximal,
  -- we need to prove that it is `≠ ⊤`
  use stabilizer_ne_top h0.nonempty h1
  -- … and that every strict over-subgroup `G` is equal to `⊤`
  intro G hG
  suffices IsPreprimitive G α from subgroup_eq_top_of_isPreprimitive hα G hG.le
  -- G acts transitively
  have := G.isPretransitive_of_stabilizer_lt hG
    (exists_mem_stabilizer_smul_eq (Nat.le_of_succ_le hα))
  apply IsPreprimitive.mk
  -- We reduce to proving that a block which is not a subsingleton is `univ`.
  intro B hB
  rw [IsTrivialBlock, or_iff_not_imp_left]
  intro hB'
  suffices sᶜ ⊆ B by
    apply hB.eq_univ_of_card_lt
    have : sᶜ.ncard ≤ B.ncard := ncard_le_ncard this
    grind
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
    grind
  -- Step 2 : A block contained in `sᶜ` is a subsingleton
  have hB_not_le_sc (B : Set α) (hB : IsBlock G B) (hBsc : B ⊆ sᶜ) :
      B.Subsingleton :=
    IsBlock.subsingleton_of_ssubset_compl_of_stabilizer_alternatingGroup_le h0
      (hBsc.ssubset_of_ne (by aesop)) -- uses Step 1
      hG.le hB
 -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s (B : Set α) (hB : IsBlock G B) (hBs : B ⊆ s) :
      B.Subsingleton :=
    have : IsPreprimitive (stabilizer G s) s :=
      stabilizer_subgroup_isPreprimitive h1 hG.le
    hB.subsingleton_of_stabilizer_lt_of_subset hB_not_le_sc hG hBs
  -- Step 4 : sᶜ ⊆ B : A block which is not a subsingleton contains `sᶜ`.
  suffices IsMultiplyPretransitive (↥(alternatingGroup α)) α (s.ncard + 1) by
    apply hB.compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl
      hG.le <;> grind
  have := isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) _ (Nat.sub_le _ _)
  grind

theorem isCoatom_stabilizer_singleton (h3 : 3 ≤ Nat.card α)
    {s : Set α} (h : s.Nonempty) (h1 : s.Subsingleton) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  have : Nontrivial α := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    grind
  obtain ⟨a, ha⟩ := h
  rw [Subsingleton.eq_singleton_of_mem h1 ha, stabilizer_singleton]
  have : IsPreprimitive (alternatingGroup α) α :=
    alternatingGroup.isPreprimitive_of_three_le_card α h3
  apply IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive

/-- `MulAction.stabilizer (alternatingGroup α) s` is a maximal subgroup of `alternatingGroup α`,
provided `s ≠ ∅`, `sᶜ ≠ ∅` and `Nat.card α ≠ 2 * s.ncard`.

This is the intransitive case of the O'Nan–Scott classification. -/
theorem isCoatom_stabilizer {s : Set α}
    (h0 : s.Nonempty) (h1 : sᶜ.Nonempty) (hs : Nat.card α ≠ 2 * ncard s) :
    IsCoatom (stabilizer (alternatingGroup α) s) := by
  rw [← ncard_add_ncard_compl s, two_mul, ne_eq, Nat.add_left_cancel_iff] at hs
  wlog hs' : ncard s < ncard sᶜ
  · rw [← stabilizer_compl]
    apply this h1 <;> rw [compl_compl] <;> grind
  · by_cases h0' : s.Nontrivial
    · apply isCoatom_stabilizer_of_ncard_lt_ncard_compl h0' hs'
    · simp only [not_nontrivial_iff] at h0'
      apply isCoatom_stabilizer_singleton _ h0 h0'
      rw [← ncard_add_ncard_compl s]
      rw [← ncard_pos] at h0 h1
      grind

end alternatingGroup
