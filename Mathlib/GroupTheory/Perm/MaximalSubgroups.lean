/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-! # Maximal subgroups of the symmetric groups

* `Equiv.Perm.isCoatom_stabilizer`:
  if neither `s : set α` nor its complementary subset is empty,
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

open scoped Pointwise

open Set

namespace Equiv.Perm

open MulAction

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

theorem IsPretransitive.of_partition {s : Set α}
    (hs : ∀ a ∈ s, ∀ b ∈ s, ∃ g : G, g • a = b)
    (hs' : ∀ a ∈ sᶜ, ∀ b ∈ sᶜ, ∃ g : G, g • a = b)
    (hG : stabilizer G s ≠ ⊤) :
    IsPretransitive G α := by
  suffices ∃ (a b : α) (g : G), a ∈ s ∧ b ∈ sᶜ ∧ g • a = b by
    obtain ⟨a, b, g, ha, hb, hgab⟩ := this
    rw [isPretransitive_iff_base a]
    intro x
    by_cases hx : x ∈ s
    · exact hs a ha x hx
    · rw [← Set.mem_compl_iff] at hx
      obtain ⟨k, hk⟩ := hs' b hb x hx
      use k * g
      rw [mul_smul, hgab, hk]
  contrapose! hG
  rw [eq_top_iff, le_stabilizer_iff_smul_le]
  rintro g _ b ⟨a, ha, hgab⟩
  by_contra hb
  exact hG a b g ha (Set.mem_compl hb) hgab

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

theorem moves_in
    (G : Subgroup (Perm α)) (t : Set α) (hGt : stabilizer (Perm α) t ≤ G) :
    ∀ a ∈ t, ∀ b ∈ t, ∃ g : G, g • a = b := by
  classical
  intro a ha b hb
  use ⟨swap a b, hGt (swap_mem_stabilizer ha hb)⟩
  rw [Subgroup.mk_smul, Perm.smul_def, swap_apply_left]

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
    exact ⟨g, hg, le_of_lt hG hg'⟩
  rcases lt_or_ge 1 sᶜ.encard with h1c | h1c'
  · obtain ⟨g, hg, hg'⟩ := this sᶜ h1c
    use g, hg
    rw [stabilizer_compl] at hg'
    exact le_of_lt hG hg'
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

theorem ofSubtype_mem_stabilizer {s : Set α} [DecidablePred fun x ↦ x ∈ s]
    (g : Perm s) :
    g.ofSubtype ∈ stabilizer (Perm α) s := by
  rw [mem_stabilizer_iff]
  ext g'
  simp_rw [mem_smul_set, Perm.smul_def]
  refine ⟨?_, fun a ↦ ?_⟩
  · rintro ⟨w, hs, rfl⟩
    simp [ofSubtype_apply_of_mem _ hs]
  · use (g⁻¹ ⟨g', a⟩)
    simp

open SubMulAction

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
  -- … and that every strict over-subgroup `G` is equal to `⊤`
  -- We know that `G` contains a swap
  obtain ⟨g, hg_swap, hg⟩ := has_swap_mem_of_lt_stabilizer s G hG
  -- By Jordan's theorem `eq_top_of_isPreprimitive_of_isSwap_mem`,
  -- it suffices to prove that `G` acts primitively
  apply subgroup_eq_top_of_isPreprimitive_of_isSwap_mem _ g hg_swap hg
  -- First, we prove that `G` acts transitively
  have : IsPretransitive G α := by
    apply IsPretransitive.of_partition G (s := s)
    · apply moves_in; exact le_of_lt hG
    · apply moves_in; rw [stabilizer_compl]; exact le_of_lt hG
    · intro h
      apply lt_irrefl G; apply lt_of_le_of_lt _ hG
      --  `G ≤ stabilizer (Equiv.Perm α) s`
      have : G = Subgroup.map G.subtype ⊤ := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [this, Subgroup.map_le_iff_le_comap]
      rw [show Subgroup.comap G.subtype (stabilizer (Perm α) s) = stabilizer G s from rfl, h]
  apply IsPreprimitive.mk
  -- We now have to prove that all blocks of `G` are trivial
  -- The proof needs 4 steps

  /- Step 1 : No block is equal to `sᶜ`
       This uses that `Nat.card s < Nat.card sᶜ`.
       In the equality case, `Nat.card s` = Nat.card sᶜ`,
       it would be possible that `sᶜ` is a block,
       and then `G` would be a wreath product,
       — this is case (b) of the O'Nan-Scott classification
       of maximal subgroups of the symmetric group -/
  have hB_ne_sc : ∀ (B : Set α) (_ : IsBlock G B), ¬B = sᶜ := by
    intro B hB hBsc
    rcases lt_or_ge (Nat.card α) (B.ncard * 2) with hB' | hB'
    · apply h0.ne_empty
      rw [← compl_univ_iff, ← hBsc]
      exact hB.eq_univ_of_card_lt hB'
    · rw [← not_lt] at hB'
      apply hB'
      rwa [← Set.ncard_add_ncard_compl B, mul_two, add_lt_add_iff_left, hBsc, compl_compl]

  -- Step 2 : A block contained in sᶜ is a subsingleton
  have hB_not_le_sc : ∀ (B : Set α) (_ : IsBlock G B) (_ : B ⊆ sᶜ), B.Subsingleton := by
    intro B hB hBsc
    rw [← inter_eq_self_of_subset_right hBsc, ← Subtype.image_preimage_val]
    apply Set.Subsingleton.image
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)) by
      apply Or.resolve_right this
      intro hB'
      apply hB_ne_sc B hB
      apply Set.Subset.antisymm hBsc
      intro x hx
      rw [← Subtype.coe_mk x hx, ← Set.mem_preimage, hB']
      apply Set.mem_univ
    -- IsTrivialBlock (Subtype.val ⁻¹' B : Set (sᶜ : Set α)),
    suffices IsPreprimitive (stabilizer G (sᶜ : Set α)) (sᶜ : Set α) by
      apply this.isTrivialBlock_of_isBlock
      let φ' : stabilizer G (sᶜ : Set α) → G := Subtype.val
      let f' : (sᶜ : Set α) →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by
          simp only [SMul.smul_stabilizer_def, φ'] }
      exact hB.preimage f'
    let φ : stabilizer G (sᶜ : Set α) → Perm (sᶜ : Set α) := MulAction.toPerm
    let f : (sᶜ : Set α) →ₑ[φ] (sᶜ : Set α) := {
      toFun := id
      map_smul' := fun g x => by
        simp only [φ, id, Perm.smul_def, toPerm_apply] }
    have hf : Function.Bijective f := Function.bijective_id
    rw [isPreprimitive_congr _ hf]
    · infer_instance
    -- Function.Surjective φ,
    classical
    intro g
    use! g.ofSubtype
    · apply le_of_lt hG
      rw [← stabilizer_compl]
      exact ofSubtype_mem_stabilizer g
    · rw [mem_stabilizer_iff]
      change Perm.ofSubtype g • sᶜ = sᶜ
      rw [← mem_stabilizer_iff]
      exact ofSubtype_mem_stabilizer g
    · ext ⟨x, hx⟩
      change Perm.ofSubtype g • x = _
      simp only [Perm.smul_def]
      rw [Perm.ofSubtype_apply_of_mem]

  -- Step 3 : A block contained in `s` is a subsingleton
  have hB_not_le_s : ∀ (B : Set α) (_ : IsBlock G B), B ⊆ s → B.Subsingleton := by
    intro B hB hBs
    suffices IsTrivialBlock (Subtype.val ⁻¹' B : Set s) by
      rcases this with hB' | hB'
      · -- trivial case
        rw [← inter_eq_self_of_subset_right hBs, ← Subtype.image_preimage_val]
        apply Set.Subsingleton.image
        exact hB'
      · -- `coe ⁻¹' B = s`
        have hBs' : B = s := by
          apply Set.Subset.antisymm hBs
          intro x hx
          rw [← Subtype.coe_mk x hx, ← Set.mem_preimage, hB']
          apply Set.mem_univ
        have : ∃ g' ∈ G, g' • s ≠ s := by
          by_contra h
          apply ne_of_lt hG
          push_neg at h
          apply le_antisymm (le_of_lt hG)
          intro g' hg'; rw [mem_stabilizer_iff]; exact h g' hg'
        obtain ⟨g', hg', hg's⟩ := this
        rcases MulAction.isBlock_iff_smul_eq_or_disjoint.mp hB ⟨g', hg'⟩ with h | h
        · -- case `g' • B = B` : absurd, since `B = s` and choice of `g'`
          absurd hg's
          rw [← hBs']; exact h
        · -- case `g' • B` disjoint from `B`
          suffices (g' • B).Subsingleton by
            apply Set.subsingleton_of_image _ B this
            apply Function.Bijective.injective
            apply MulAction.bijective
          apply hB_not_le_sc ((⟨g', hg'⟩ : G) • B)
          · exact IsBlock.translate ⟨g', hg'⟩ hB
          rw [← hBs']
          apply Disjoint.subset_compl_right h
    -- `IsTrivialBlock (coe ⁻¹' B : Set s)`
    suffices IsPreprimitive (stabilizer G s) s by
      apply this.isTrivialBlock_of_isBlock
      -- `IsBlock (coe ⁻¹' B : Set s)`
      let φ' : stabilizer G s → G := Subtype.val
      let f' : s →ₑ[φ'] α := {
        toFun := Subtype.val
        map_smul' := fun ⟨m, _⟩ x => by
          simp only [SMul.smul_stabilizer_def, φ'] }
      apply MulAction.IsBlock.preimage f' hB
    -- `IsPreprimitive (stabilizer G s) s`
    let φ : stabilizer G s → Perm s := toPerm
    let f : s →ₑ[φ] s := {
        toFun := id
        map_smul' := fun g x => by
          simp only [φ, id, Perm.smul_def, toPerm_apply] }
    have hf : Function.Bijective f := Function.bijective_id
    rw [isPreprimitive_congr _ hf]
    · infer_instance
    -- Function.Surjective φ
    classical
    intro g
    use! Perm.ofSubtype g
    · apply le_of_lt hG
      apply ofSubtype_mem_stabilizer
    · apply ofSubtype_mem_stabilizer
    · ext ⟨x, hx⟩
      change ofSubtype g • x = _
      simp only [Perm.smul_def]
      rw [ofSubtype_apply_of_mem]
  intro B hB
  unfold IsTrivialBlock
  rw [or_iff_not_imp_left]
  intro hB'
  obtain ⟨a, ha, ha'⟩ :=
    Set.not_subset_iff_exists_mem_notMem.mp fun h => hB' ((hB_not_le_sc B hB) h)
  rw [Set.notMem_compl_iff] at ha'
  obtain ⟨b, hb, hb'⟩ :=
    Set.not_subset_iff_exists_mem_notMem.mp fun h => hB' ((hB_not_le_s B hB) h)
  rw [← Set.mem_compl_iff] at hb'
  have hsc_le_B : sᶜ ⊆ B := by
    intro x hx'
    suffices ∃ k : fixingSubgroup (Perm α) s, k • b = x by
      obtain ⟨⟨k, hk⟩, hkbx : k • b = x⟩ := this
      suffices k • B = B by
        rw [← hkbx, ← this, Set.smul_mem_smul_set_iff]
        exact hb
      -- `k • B = B`
      apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨k, ?_⟩)
      · refine ⟨a, ⟨?_, ha⟩⟩
        rw [mem_fixingSubgroup_iff] at hk
        rw [← hk a ha']
        exact Set.smul_mem_smul_set ha
      · -- `↑k ∈ G`
        apply le_of_lt hG
        exact MulAction.fixingSubgroup_le_stabilizer _ _ hk
    · -- `∃ (k : fixingSubgroup (Perm α) s), k • b = x`
      suffices
        IsPretransitive (fixingSubgroup (Perm α) s)
          (ofFixingSubgroup (Perm α) s) by
        obtain ⟨k, hk⟩ :=
          exists_smul_eq (fixingSubgroup (Perm α) s)
           (⟨b, hb'⟩ : ofFixingSubgroup (Perm α) s) ⟨x, hx'⟩
        use k
        rw [← Subtype.coe_inj, val_smul] at hk
        exact hk
      -- Prove pretransitivity…
      rw [← is_one_pretransitive_iff]
      have _ :  IsMultiplyPretransitive (Perm α) α (s.ncard + 1) := by
        exact isMultiplyPretransitive α (s.ncard + 1)
      apply ofFixingSubgroup.isMultiplyPretransitive
        (Perm α) s rfl
  -- Conclusion of the proof : `B = univ`
  rw [← Set.top_eq_univ, eq_top_iff]
  intro x _
  obtain ⟨b, hb⟩ := h1
  obtain ⟨⟨g, hg⟩, hgbx : g • b = x⟩ := exists_smul_eq G b x
  suffices g • B = B by
    rw [← hgbx, ← this, Set.smul_mem_smul_set_iff]
    exact hsc_le_B hb
  -- `g • B = B`
  apply isBlock_iff_smul_eq_of_nonempty.mp hB (g := ⟨g, hg⟩)
  rw [Subgroup.mk_smul]
  apply nonempty_inter_of_lt_ncard_add_ncard
  -- `card B + card (g • B) = card B + card B`
  -- ... ≥ `card sᶜ + card sᶜ`
  -- ... > `card s + card s ᶜ = card α`
  rw [← Set.ncard_add_ncard_compl s]
  apply Nat.lt_of_lt_of_le
  · rw [Nat.add_lt_add_iff_right]
    exact hα
  · simp only [Set.ncard_smul_set, ← two_mul]
    apply Nat.mul_le_mul_left
    exact Set.ncard_le_ncard hsc_le_B (Set.toFinite B)

/-- `MulAction.stabilizer (Perm α) s` is a maximal subgroup of `Perm α`,
provided `s` and `sᶜ` are nonempty, and `Nat.card α ≠ 2 * Nat.card s`. -/
theorem isCoatom_stabilizer {s : Set α}
    (h0 : s.Nonempty) (h1 : sᶜ.Nonempty)
    (hα : Nat.card α ≠ 2 * s.ncard) :
    IsCoatom (stabilizer (Perm α) s) := by
  obtain hs | hs | hs := Nat.lt_trichotomy s.ncard sᶜ.ncard
  · exact isCoatom_stabilizer_of_ncard_lt_ncard_compl h0 hs
  · contrapose! hα
    rw [← Set.ncard_add_ncard_compl s, two_mul, ← hs]
  · rw [← stabilizer_compl]
    apply isCoatom_stabilizer_of_ncard_lt_ncard_compl h1
    rwa [compl_compl]

end Equiv.Perm
