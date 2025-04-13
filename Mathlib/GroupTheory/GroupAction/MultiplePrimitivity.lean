/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module multiple_primitivity
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

open scoped BigOperators Pointwise Cardinal

-- open scoped Classical

section MultiplePrimitivity

namespace MulAction

open SubMulAction

variable (M α : Type*) [Group M] [MulAction M α]

abbrev IsMultiplyPreprimitive (n : ℕ) :=
  IsMultiplyPretransitive M α n ∧
    ∀ (s : Set α), s.encard + 1 = n →
      IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s)

/-- Any action is 0-fold preprimitive -/
theorem is_zero_preprimitive : IsMultiplyPreprimitive M α 0 :=
  ⟨MulAction.is_zero_pretransitive, fun s ↦ by simp⟩

/-- An action is preprimitive iff it is 1-preprimitive -/
theorem is_one_preprimitive_iff :
    IsMultiplyPreprimitive M α 1 ↔ IsPreprimitive M α := by
  unfold IsMultiplyPreprimitive
  simp only [is_one_pretransitive_iff]
  have H := (isPreprimitive_congr
      (of_fixingSubgroupEmpty_mapScalars_surjective  (M := M))
      (ofFixingSubgroupEmpty_equivariantMap_bijective α))
  constructor
  · exact fun ⟨_, h1'⟩ ↦ H.mp (h1' ∅ (by simp))
  · intro h
    refine ⟨h.toIsPretransitive, ?_⟩
    intro s hs
    suffices s = ∅ by
      rw [this]
      exact H.mpr h
    rw [← Set.encard_eq_zero]
    suffices s.encard ≠ (⊤ : ℕ∞) by
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp this
      rw [← hm, ← Nat.cast_one, ← ENat.coe_add, Nat.cast_inj, Nat.add_eq_right] at hs
      simp [← hm, hs]
    exact fun h ↦ by simp [h] at hs

/-- A multiply preprimitive action is multiply pretransitive -/
theorem IsMultiplyPreprimitive.toIsMultiplyPretransitive {n : ℕ}
    (h : IsMultiplyPreprimitive M α n) : IsMultiplyPretransitive M α n :=
  h.left

/-- A pretransitive  action is n.succ-fold preprimitive  iff
  the action of stabilizers is n-fold preprimitive -/
theorem stabilizer.isMultiplyPreprimitive [IsPretransitive M α] {n : ℕ} (hn : 1 ≤ n) {a : α} :
    IsMultiplyPreprimitive M α n.succ ↔
      IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  constructor
  · rintro ⟨htrans, hprim⟩
    rcases Nat.lt_or_ge n 1 with h0 | h1
    · rw [Nat.lt_one_iff] at h0
      rw [h0]
      apply is_zero_preprimitive
    refine ⟨ofStabilizer.isMultiplyPretransitive.mp htrans, ?_⟩
    intro s hs
    have : IsPreprimitive ↥(fixingSubgroup M (insert a (Subtype.val '' s)))
      ↥(ofFixingSubgroup M (insert a (Subtype.val '' s))) := by
      apply hprim _
      rw [Set.encard_insert_of_not_mem, Subtype.coe_injective.encard_image, hs, Nat.cast_succ]
      intro ha
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at ha
      obtain ⟨b, _⟩ := ha
      apply b
      simp only [Set.mem_singleton_iff]
    apply IsPreprimitive.of_surjective
      (equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective a s).surjective
  · rintro ⟨htrans, hprim⟩
    refine ⟨ofStabilizer.isMultiplyPretransitive.mpr htrans, ?_⟩
    suffices ∀ (s : Set α) (_ : s.encard + 1 = n.succ) (_ : a ∈ s),
        IsPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) by
      intro s hs
      have : ∃ b : α, b ∈ s := by
        rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
        intro h
        apply not_lt.mpr hn
        rw [h, Set.encard_empty, zero_add, ← Nat.cast_one, Nat.cast_inj, Nat.succ_inj'] at hs
        simp only [← hs, zero_lt_one]
      obtain ⟨b, hb⟩ := this
      obtain ⟨g, hg : g • b = a⟩ := exists_smul_eq M b a
      rw [isPreprimitive_ofFixingSubgroup_conj_iff (g := g)]
      refine this (g • s) ?_ ⟨b, hb, hg⟩
      · rw [← hs]
        congr 1
        exact Function.Injective.encard_image (MulAction.injective g) s
    intro s hs has
    let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s
    have hst : s = insert a (Subtype.val '' t) := by
      ext x
      constructor
      · intro hxs
        by_cases hxa : x = a
        · rw [hxa]; apply Set.mem_insert
        · exact Set.mem_insert_of_mem _
            ⟨⟨x, hxa⟩, by simp only [t, Set.mem_preimage]; exact hxs, rfl⟩
      · intro hxat
        rcases Set.mem_insert_iff.mp hxat with hxa | hxt
        · rw [hxa]; exact has
        · obtain ⟨y, hy, rfl⟩ := hxt
          simpa only using hy
    rw [hst]
    rw [isPreprimitive_fixingSubgroup_insert_iff]
    · apply hprim t
      apply ENat.add_left_injective_of_ne_top ENat.one_ne_top
      rw [hst, Set.encard_insert_of_not_mem _] at hs
      · simpa [Subtype.coe_injective.encard_image] using hs
      · rintro ⟨b, hb⟩
        apply b.prop
        simp [hb]

/-- The fixator of a subset of cardinal d in an n-primitive action
  acts (n-d) primitively on the remaining (d ≤ n) -/
theorem remaining_primitivity
    {m n : ℕ} {s : Set α} [Finite s] (hs : n = m + s.ncard) (hs' : s.ncard + m = n)
    (hmp : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m := by
  have _ : IsMultiplyPretransitive M α n := hmp.1
  have hprim := hmp.2
  refine ⟨ofFixingSubgroup.isMultiplyPretransitive s hs', ?_⟩
  intro t ht
  let t' : Set α := Subtype.val '' t
  have htt' : t = Subtype.val ⁻¹' t' := by
    apply symm
    apply Set.preimage_image_eq
    exact Subtype.coe_injective
  rw [htt']
  have := hmp.2 s
  let f := map_ofFixingSubgroupUnion M s t'
  rw [← isPreprimitive_congr
    (fixingSubgroup_union_to_fixingSubgroup_fixingSubgroup_bijective M s t').surjective
    (map_ofFixingSubgroupUnion_bijective M s t') ]
  apply hprim
  rw [Set.encard_union_eq _]
  · rw [Subtype.coe_injective.encard_image, add_assoc, ht, hs, add_comm, Nat.cast_add]
    rw [Set.Finite.cast_ncard_eq]
    exact Set.toFinite s
  · rw [Set.disjoint_iff]
    intro a
    rintro ⟨hbs, ⟨b, _, rfl⟩⟩
    exfalso
    exact b.prop hbs

/-- n.succ-fold pretransitivity implies n-fold preprimitivity -/
theorem isMultiplyPreprimitive_of_multiply_pretransitive_succ {n : ℕ}
    (hα : ↑n.succ ≤ ENat.card α) (h : IsMultiplyPretransitive M α n.succ) :
    IsMultiplyPreprimitive M α n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  -- n = 0
  · rw [hn]
    exact is_zero_preprimitive M α
  -- n > 0
  · refine ⟨isMultiplyPretransitive_of_le' (Nat.le_succ n) hα, ?_⟩
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    rw [hm]
    intro s hs
    apply isPreprimitive_of_is_two_pretransitive
    simp only [Nat.succ_eq_add_one, zero_add, Nat.cast_add, Nat.cast_one] at hs
    -- rw [add_comm _ m, Nat.cast_add, ← Nat.cast_one, WithTop.add_eq_add_iff] at hs
    have hs' : s.encard = m := by
      rw [add_comm 1] at hs
      exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hs
    have : Finite s := Set.finite_of_encard_eq_coe hs'
    have hs'' : s.ncard = m := by simp [Set.ncard, hs']
    apply ofFixingSubgroup.isMultiplyPretransitive (M := M) s (n := n.succ)
    simp only [hs'', hm, Nat.succ_eq_add_one]; ring



/-- An n-fold preprimitive action is m-fold preprimitive for m ≤ n -/
theorem isMultiplyPreprimitive_of_higher
    {n : ℕ} {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ ENat.card α)
    (hn : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive M α m := by
  -- induction on n
  induction n with
  -- n = 0 : implies m = 0
  | zero =>
    rw [Nat.eq_zero_of_le_zero hmn]
    exact hn
  -- induction step
  | succ n hrec =>
    rcases Nat.eq_or_lt_of_le hmn with hmn | hmn'
    -- m = n + 1 = this is hn
    · rw [hmn]; exact hn
    -- m < n + 1 : use induction hypothesis
    · apply hrec (Nat.lt_succ_iff.mp hmn')
      · refine le_trans ?_ hα; rw [ENat.coe_le_coe]; exact Nat.le_succ n
      -- get one step by transitivity
      · exact isMultiplyPreprimitive_of_multiply_pretransitive_succ M α hα hn.left

variable {M α}

theorem isMultiplyPreprimitive_congr
    {N β : Type*} [Group N] [MulAction N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hf : Function.Bijective f) {n : ℕ}
    (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive N β n := by
  have _ := h.1
  refine ⟨IsPretransitive.of_embedding hf.surjective, ?_⟩
  intro t ht
  let s := f ⁻¹' t
  have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
  let φ' : fixingSubgroup M s → fixingSubgroup N t := fun ⟨m, hm⟩ ↦
    ⟨φ m, fun ⟨y, hy⟩ => by
      rw [← hs', Set.mem_image] at hy
      obtain ⟨x, hx, hx'⟩ := hy
      simp only [Subtype.coe_mk]
      rw [← hx', ← map_smulₛₗ]
      apply congr_arg
      rw [mem_fixingSubgroup_iff] at hm
      exact hm x hx⟩
  let f' : SubMulAction.ofFixingSubgroup M s →ₑ[φ'] SubMulAction.ofFixingSubgroup N t :=
    { toFun := fun ⟨x, hx⟩ => ⟨f.toFun x, fun h => hx (Set.mem_preimage.mp h)⟩
      map_smul' := fun ⟨m, hm⟩ ⟨x, hx⟩ =>
        by
        rw [← SetLike.coe_eq_coe]
        exact f.map_smul' m x }
  have hf' : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hf.right y
    use ⟨x, ?_⟩
    · simpa only [f', ← Subtype.coe_inj] using hx
    · intro h
      apply hy
      rw [← hs']
      exact ⟨x, h, hx⟩
  have := h.2 s (by
    rw [← ht, ← hs', hf.injective.encard_image])
  exact IsPreprimitive.of_surjective (f := f') (φ := φ') hf'

end MulAction

end MultiplePrimitivity


