/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-! # Maximal subgroups of the symmetric groups

* `Equiv.Perm.isCoatom_stabilizer`:
  if neither `s : Set α` nor its complementary subset is empty,
  and the cardinality of `s` is not half of that of `α`,
  then `MulAction.stabilizer (Equiv.Perm α) s` is
  a maximal subgroup of the symmetric group `Equiv.Perm α`.

  This is the *intransitive case* of the O'Nan-Scott classification.

## TODO

  * Application to primitivity of the action
    of `Equiv.Perm α` on finite combinations of `α`.

  * Formalize the other cases of the classification.
    The next one should be the *imprimitive case*.

## Reference

The argument is taken from [M. Liebeck, C. Praeger, J. Saxl,
*A classification of the maximal subgroups of the finite
alternating and symmetric groups*, 1987][LiebeckPraegerSaxl-1987].
-/

@[expose] public section

open scoped Pointwise

open Set

variable {M α : Type*} [Group M] [MulAction M α] {s : Set α}

namespace MulAction

open Equiv

variable (s) in
/- Note : Under the hypothesis, multiple transitivity would also hold. -/
/-- In the permutation group, the stabilizer of any set
acts primitively on that set. -/
theorem isPreprimitive_stabilizer_of_surjective
    (hs : Function.Surjective (toPerm : stabilizer M s → Perm s)) :
    IsPreprimitive (stabilizer M s) s := by
  let φ : stabilizer M s → Perm s := toPerm
  let f : s →ₑ[φ] s := {
    toFun := id
    map_smul' _ _ := rfl }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_congr hs hf]
  infer_instance

/-- A (mostly trivial) primitivity criterion for stabilizers. -/
theorem isPreprimitive_stabilizer_subgroup [IsPreprimitive (stabilizer M s) s]
    {G : Subgroup M} (hG : stabilizer M s ≤ G) :
    IsPreprimitive (stabilizer G s) s :=
  let φ (g : stabilizer M s) : stabilizer G s :=
    ⟨⟨g, hG g.prop⟩, g.prop⟩
  let f : s →ₑ[φ] s := {
      toFun := id
      map_smul' _ _ := rfl }
  IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem IsPretransitive.of_partition
    (hs : ∀ a ∈ s, ∀ b ∈ s, ∃ g : M, g • a = b)
    (hs' : ∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g : M, g • a = b)
    (hM : stabilizer M s ≠ ⊤) :
    IsPretransitive M α := by
  suffices ∃ (a b : α) (g : M), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b by
    obtain ⟨a, b, g, ha, hb, hgab⟩ := this
    rw [isPretransitive_iff_base a]
    intro x
    by_cases hx : x ∈ s
    · exact hs a ha x hx
    · rw [← Set.mem_compl_iff] at hx
      obtain ⟨k, hk⟩ := hs' b hb x hx
      use k * g
      rw [mul_smul, hgab, hk]
  contrapose! hM
  rw [eq_top_iff, le_stabilizer_iff_smul_le]
  rintro g _ b ⟨a, ha, hgab⟩
  by_contra hb
  exact hM a b g ha (Set.mem_compl hb) hgab

end MulAction

namespace Equiv.Perm

open MulAction

theorem ofSubtype_mem_stabilizer [DecidablePred fun x ↦ x ∈ s] (g : Perm s) :
    g.ofSubtype ∈ stabilizer (Perm α) s := by
  rw [mem_stabilizer_iff]
  ext g'
  simp_rw [mem_smul_set, Perm.smul_def]
  refine ⟨?_, fun a ↦ ?_⟩
  · rintro ⟨w, hs, rfl⟩
    simp [ofSubtype_apply_of_mem _ hs]
  · use (g⁻¹ ⟨g', a⟩)
    simp

theorem swap_mem_stabilizer [DecidableEq α]
    {a b : α} {s : Set α} (ha : a ∈ s) (hb : b ∈ s) :
    swap a b ∈ stabilizer (Perm α) s := by
  suffices swap a b • s ⊆ s by
    rw [mem_stabilizer_iff]
    apply Set.Subset.antisymm this
    exact Set.subset_smul_set_iff.mpr this
  rintro _ ⟨x, hx, rfl⟩
  by_cases h : x ∈ ({a, b} : Set α)
  · aesop
  · have := swap_apply_of_ne_of_ne (a := a) (b := b) (x := x)
    aesop

theorem exists_mem_stabilizer_smul_eq :
    ∀ a ∈ s, ∀ b ∈ s, ∃ g ∈ stabilizer (Perm α) s, g • a = b := by
  intro a ha b hb
  classical
  exact ⟨swap a b, swap_mem_stabilizer ha hb, swap_apply_left a b⟩

theorem stabilizer.surjective_toPerm (s : Set α) :
    Function.Surjective (toPerm : stabilizer (Perm α) s → Perm s) := fun g ↦ by
  classical
  use! Perm.ofSubtype g
  · apply ofSubtype_mem_stabilizer
  · aesop

/-- In the permutation group, the stabilizer of a set acts primitively on that set. -/
instance stabilizer_isPreprimitive (s : Set α) :
    IsPreprimitive (stabilizer (Perm α) s) s :=
  isPreprimitive_stabilizer_of_surjective s (stabilizer.surjective_toPerm s)

theorem stabilizer_ne_top_of_nonempty_of_nonempty_compl
    {s : Set α} (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    stabilizer (Perm α) s ≠ ⊤ := by
  classical
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := hsc
  intro h
  rw [Set.mem_compl_iff] at hb; apply hb
  have hg : swap a b ∈ stabilizer (Perm α) s := by simp_all
  rw [mem_stabilizer_iff] at hg
  rw [← hg, Set.mem_smul_set]
  aesop

theorem has_swap_mem_of_lt_stabilizer [DecidableEq α]
    (s : Set α) (G : Subgroup (Perm α))
    (hG : stabilizer (Perm α) s < G) :
    ∃ g : Perm α, g.IsSwap ∧ g ∈ G := by
  have : ∀ (t : Set α) (_ : 1 < t.encard), ∃ (g : Perm α),
      g.IsSwap ∧ g ∈ stabilizer (Perm α) t := by
    intro t ht
    rw [Set.one_lt_encard_iff] at ht
    obtain ⟨a, b, ha, hb, h⟩ := ht
    use swap a b, Perm.swap_isSwap_iff.mpr h, swap_mem_stabilizer ha hb
  rcases lt_or_ge 1 s.encard with h1 | h1'
  · obtain ⟨g, hg, hg'⟩ := this s h1
    exact ⟨g, hg, hG.le hg'⟩
  rcases lt_or_ge 1 sᶜ.encard with h1c | h1c'
  · obtain ⟨g, hg, hg'⟩ := this sᶜ h1c
    use g, hg
    rw [stabilizer_compl] at hg'
    exact hG.le hg'
  have hα : Set.encard (_root_.Set.univ : Set α) = 2 := by
    rw [← Set.encard_add_encard_compl s]
    have : (1 + 1 : ENat) = 2 := by norm_num
    convert this <;>
    · apply le_antisymm
      · assumption
      rw [one_le_encard_iff_nonempty, Set.nonempty_iff_ne_empty]
      aesop
  have _ : Finite α := by
    rw [finite_iff_nonempty_fintype]
    refine univ_finite_iff_nonempty_fintype.mp ?_
    exact finite_of_encard_eq_coe hα
  have hα : Nat.card α = 2 := by
    rw [← ENat.card_coe_set_eq, ENat.card_eq_coe_natCard, Nat.card_coe_set_eq, ncard_univ] at hα
    exact ENat.coe_inj.mp hα
  have hα2 : Fact (Nat.card (Perm α)).Prime := by
    apply Fact.mk
    rw [Nat.card_perm, hα, Nat.factorial_two]
    exact Nat.prime_two
  cases G.eq_bot_or_eq_top_of_prime_card with
  | inl h =>
    exfalso; exact ne_bot_of_gt hG h
  | inr h =>
    rw [h, ← stabilizer_univ_eq_top (Perm α) α]
    apply this
    simp_all

lemma _root_.Subgroup.isPretransitive_of_stabilizer_lt
    {G : Subgroup M} (hG : stabilizer M s < G)
    (moves : ∀ {s : Set α}, ∀ a ∈ s, ∀ b ∈ s, ∃ g ∈ stabilizer M s, g • a = b) :
    IsPretransitive G α := by
  apply IsPretransitive.of_partition (s := s)
  · intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := moves a ha b hb
    exact ⟨⟨g, hG.le hg⟩, rfl⟩
  · intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := moves a ha b hb
    rw [stabilizer_compl] at hg
    exact ⟨⟨g, hG.le hg⟩, rfl⟩
  · contrapose! hG
    apply not_lt_of_ge
    --  `G ≤ stabilizer (Equiv.Perm α) s`
    have : G = Subgroup.map G.subtype ⊤ := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [this, Subgroup.map_le_iff_le_comap]
    rw [show Subgroup.comap G.subtype (stabilizer M s) = stabilizer G s from rfl, hG]

end Equiv.Perm

namespace MulAction.IsBlock

open Equiv Equiv.Perm MulAction SubMulAction

lemma subsingleton_of_ssubset_of_stabilizer_le
    {B : Set α} (hB_ss_sc : B ⊂ s) (hB : IsBlock M B)
    (hG : Function.Surjective
      (MulAction.toPerm : stabilizer M (s : Set α) → Perm (s : Set α))) :
    B.Subsingleton := by
  rw [← inter_eq_self_of_subset_right (subset_of_ssubset hB_ss_sc), ← Subtype.image_preimage_val]
  apply Set.Subsingleton.image
  suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (s : Set α)) by
    apply Or.resolve_right this
    rw [preimage_eq_univ_iff, Subtype.range_coe_subtype]
    exact not_subset_of_ssubset hB_ss_sc
  suffices IsPreprimitive (stabilizer M (s : Set α)) (s : Set α) by
    apply this.isTrivialBlock_of_isBlock
    let φ' : stabilizer M (s : Set α) → M := Subtype.val
    let f' : (s : Set α) →ₑ[φ'] α := {
      toFun := Subtype.val
      map_smul' _ _ := rfl }
    exact hB.preimage f'
  let φ : stabilizer M (s : Set α) → Perm (s : Set α) := MulAction.toPerm
  let f : (s : Set α) →ₑ[φ] (s : Set α) := {
    toFun := id
    map_smul' _ _ := rfl }
  have hf : Function.Bijective f := Function.bijective_id
  rw [isPreprimitive_congr hG hf]
  infer_instance

lemma subsingleton_of_ssubset_of_stabilizer_Perm_le
    {B : Set α} {G : Subgroup (Perm α)} (hB : IsBlock G B)
    (hB_ss_sc : B ⊂ s) (hG : stabilizer (Perm α) s ≤ G) :
    B.Subsingleton := by
  apply hB.subsingleton_of_ssubset_of_stabilizer_le hB_ss_sc
  intro g
  obtain ⟨⟨k, hk⟩, rfl⟩ := stabilizer.surjective_toPerm s g
  let h : G := ⟨k, hG hk⟩
  have : h ∈ stabilizer G s := by aesop
  exact ⟨⟨h, this⟩, rfl⟩

lemma subsingleton_of_stabilizer_lt_of_subset {B : Set α}
    {G : Subgroup M} [IsPreprimitive (stabilizer G s) s]
    (hB : IsBlock G B)
    (hB_not_le_sc : ∀ (B : Set α), IsBlock G B → B ⊆ sᶜ → B.Subsingleton)
    (hG : stabilizer M s < G) (hBs : B ⊆ s) :
    B.Subsingleton := by
  suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
    rcases this with hB' | hB'
    · -- trivial case
      rw [← inter_eq_self_of_subset_right hBs, ← Subtype.image_preimage_val]
      apply Set.Subsingleton.image hB'
    · -- `Subtype.val ⁻¹' B = s`
      have hBs' : B = s := Set.Subset.antisymm hBs (by aesop)
      subst hBs'
      obtain ⟨g', hg', hg's⟩ := SetLike.exists_of_lt hG
      have h := (isBlock_iff_smul_eq_or_disjoint.mp hB ⟨g', hg'⟩).resolve_left hg's
      suffices (g' • B).Subsingleton by
        exact subsingleton_of_image (MulAction.injective g') B this
      apply hB_not_le_sc (⟨g', hg'⟩ • B) (hB.translate _)
      exact Disjoint.subset_compl_right h
  -- `IsTrivialBlock (Subtype.val ⁻¹' B : Set s)`
  suffices IsPreprimitive (stabilizer G s) s by
    apply this.isTrivialBlock_of_isBlock
    -- `IsBlock (Subtype.val ⁻¹' B : Set s)`
    let φ' : stabilizer G s → G := Subtype.val
    let f' : s →ₑ[φ'] α := {
      toFun := Subtype.val
      map_smul' _ _ := rfl }
    apply MulAction.IsBlock.preimage f' hB
  infer_instance

variable [Finite α]

lemma compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl
    [IsMultiplyPretransitive M α (s.ncard + 1)]
    {G : Subgroup M} (hG : stabilizer M s ≤ G)
    {B : Set α}
    (hBs : ¬ B ⊆ s) (hBsc : ¬ B ⊆ sᶜ) (hB : IsBlock G B) :
    sᶜ ⊆ B := by
  have : ∃ a : α, a ∈ B ∧ a ∈ s := by grind
  obtain ⟨a, ha, ha'⟩ := this
  have : ∃ b : α, b ∈ B ∧ b ∈ sᶜ := by grind
  obtain ⟨b, hb, hb'⟩ := this
  intro x hx'
  suffices ∃ k : fixingSubgroup M s, k • b = x by
    obtain ⟨⟨k, hk⟩, rfl⟩ := this
    suffices k • B = B from this.le (smul_mem_smul_set hb)
    -- `k • B = B`
    apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨k, ?_⟩)
    · refine ⟨a, ?_, ha⟩
      rw [mem_fixingSubgroup_iff] at hk
      rw [← hk a ha']
      exact Set.smul_mem_smul_set ha
    · -- `k ∈ G`
      apply hG
      exact MulAction.fixingSubgroup_le_stabilizer _ _ hk
  · -- `∃ (k : fixingSubgroup (Perm α) s), k • b = x`
    suffices h : IsPretransitive (fixingSubgroup M s) (ofFixingSubgroup M s) by
      obtain ⟨k, hk⟩ := h.exists_smul_eq (⟨b, hb'⟩ : ofFixingSubgroup M s) ⟨x, hx'⟩
      rw [← Subtype.coe_inj, val_smul] at hk
      exact ⟨k, hk⟩
    -- Prove pretransitivity…
    rw [← is_one_pretransitive_iff]
    apply ofFixingSubgroup.isMultiplyPretransitive M s rfl

end MulAction.IsBlock

namespace Equiv.Perm

open MulAction Equiv

variable [Finite α]

theorem isCoatom_stabilizer_of_ncard_lt_ncard_compl
    {s : Set α} (h0 : s.Nonempty) (hα : s.ncard < sᶜ.ncard) :
    IsCoatom (stabilizer (Perm α) s) := by
  classical
  have h1 : sᶜ.Nonempty := nonempty_iff_ne_empty.mpr (by aesop)
  have : Fintype α := Fintype.ofFinite α
  -- To prove that `stabilizer (Perm α) s` is maximal,
  -- we need to prove that it is `≠ ⊤`
  refine ⟨stabilizer_ne_top_of_nonempty_of_nonempty_compl h0 h1, fun G hG ↦ ?_⟩
  have hG' : stabilizer (Perm α) sᶜ < G := by rwa [stabilizer_compl]
  -- … and that every strict over-subgroup `G` is equal to `⊤`
  -- We know that `G` contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_mem_of_lt_stabilizer s G hG
  -- By Jordan's theorem `subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`,
  -- it suffices to prove that `G` acts primitively
  apply subgroup_eq_top_of_isPreprimitive_of_isSwap_mem _ g hg_swap hg
  -- First, we prove that `G` acts transitively
  have := G.isPretransitive_of_stabilizer_lt hG exists_mem_stabilizer_smul_eq
  apply IsPreprimitive.mk
  -- We now have to prove that all blocks of `G` are trivial
  -- We reduce to proving that a block which is not a subsingleton is `univ`.
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'
  suffices sᶜ ⊆ B by
    apply hB.eq_univ_of_card_lt
    have : sᶜ.ncard ≤ B.ncard := ncard_le_ncard this
    rw [← Set.ncard_add_ncard_compl s]
    linarith
  -- The proof needs 4 steps
  /- Step 1 : `sᶜ` is not a block.
       This uses that `Nat.card s < Nat.card sᶜ`.
       In the equality case, `Nat.card s` = Nat.card sᶜ`,
       it would be possible that `sᶜ` is a block,
       and then `G` would be a wreath product,
       — this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the symmetric group -/
  have not_isBlock_sc : ¬ IsBlock G sᶜ := fun hsc ↦ by
    rcases lt_or_ge (Nat.card α) (sᶜ.ncard * 2) with hB' | hB'
    · apply h0.ne_empty
      rw [← compl_univ_iff]
      exact hsc.eq_univ_of_card_lt hB'
    · rw [← not_lt] at hB'
      apply hB'
      rwa [← Set.ncard_add_ncard_compl sᶜ, mul_two, add_lt_add_iff_left, compl_compl]
  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc (B : Set α) (hB : IsBlock G B) (hBsc : B ⊆ sᶜ) :
      B.Subsingleton :=
    -- uses Step 1
    hB.subsingleton_of_ssubset_of_stabilizer_Perm_le (hBsc.ssubset_of_ne (by aesop)) hG'.le
  -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s (B : Set α) (hB : IsBlock G B) (hBs : B ⊆ s) : B.Subsingleton :=
    have := isPreprimitive_stabilizer_subgroup hG.le
    hB.subsingleton_of_stabilizer_lt_of_subset hB_not_le_sc hG hBs
  -- Step 4 : `sᶜ ⊆ B`
  have _ := isMultiplyPretransitive α (s.ncard + 1)
  apply IsBlock.compl_subset_of_stabilizer_le_of_not_subset_of_not_subset_compl hG.le <;> grind

/-- `MulAction.stabilizer (Perm α) s` is a maximal subgroup of `Perm α`,
provided `s` and `sᶜ` are nonempty, and `Nat.card α ≠ 2 * Nat.card s`.

This is the intransitive case of the O'Nan–Scott classification. -/
theorem isCoatom_stabilizer {s : Set α}
    (hs_nonempty : s.Nonempty) (hsc_nonempty : sᶜ.Nonempty)
    (hα : Nat.card α ≠ 2 * s.ncard) :
    IsCoatom (stabilizer (Perm α) s) := by
  obtain h | h | h := Nat.lt_trichotomy s.ncard sᶜ.ncard
  · exact isCoatom_stabilizer_of_ncard_lt_ncard_compl hs_nonempty h
  · contrapose! hα
    rw [← Set.ncard_add_ncard_compl s, two_mul, ← h]
  · rw [← stabilizer_compl]
    apply isCoatom_stabilizer_of_ncard_lt_ncard_compl hsc_nonempty
    rwa [compl_compl]

end Equiv.Perm
