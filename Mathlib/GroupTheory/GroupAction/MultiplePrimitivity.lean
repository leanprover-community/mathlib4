/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup

/-! # Multiply preprimitive actions

TODO :
 * Add documentation
 * Is using `IsMultiplyPreprimitive` as a class so useful ?
 * additivize (doesn't work!)

-/

open scoped BigOperators Pointwise Cardinal

namespace MulAction

open SubMulAction

/-- A group action is n-multiply preprimitive  if is is n-multiply transitive
  and if, when n ≥ 1, for every set `s` of cardinality n - 1,
  the action of `fixingSubgroup M s` on the complement of `s` is preprimitive. -/
class IsMultiplyPreprimitive (M α : Type*) [Group M] [MulAction M α] (n : ℕ) where
  /-- An n-preprimitive action is n-pretransitive -/
  isMultiplyPretransitive (M α n) : IsMultiplyPretransitive M α n
  /-- In an n-preprimitive action, the action of `fixingSubgroup M s` on `ofFixingSubgroup M s`
  is preprimitive, for all sets `s` such that `s.encard + 1 = n` -/
  isPreprimitive_ofFixingSubgroup (M n) {s : Set α} (hs : s.encard + 1 = n) :
    IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s)

variable (M α : Type*) [Group M] [MulAction M α]

instance (n : ℕ) [IsMultiplyPreprimitive M α n] :
    IsMultiplyPretransitive M α n :=
  IsMultiplyPreprimitive.isMultiplyPretransitive M α n

/-- Any action is 0-fold preprimitive -/
theorem is_zero_preprimitive : IsMultiplyPreprimitive M α 0 where
  isMultiplyPretransitive := MulAction.is_zero_pretransitive
  isPreprimitive_ofFixingSubgroup hs := by simp at hs

/-- An action is preprimitive iff it is 1-preprimitive -/
theorem is_one_preprimitive_iff :
    IsMultiplyPreprimitive M α 1 ↔ IsPreprimitive M α := by
  have H := (isPreprimitive_congr
      (of_fixingSubgroupEmpty_mapScalars_surjective  (M := M))
      (ofFixingSubgroupEmpty_equivariantMap_bijective α))
  constructor
  · intro H1
    rw [← H]
    apply H1.isPreprimitive_ofFixingSubgroup (by simp)
  · intro h
    exact {
      isMultiplyPretransitive := is_one_pretransitive_iff.mpr h.toIsPretransitive
      isPreprimitive_ofFixingSubgroup {s} hs := by
        suffices s = ∅ by
          rw [this]
          exact H.mpr h
        rw [← Set.encard_eq_zero]
        suffices s.encard ≠ (⊤ : ℕ∞) by
          obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp this
          rw [← hm, ← Nat.cast_one, ← ENat.coe_add, Nat.cast_inj, Nat.add_eq_right] at hs
          simp [← hm, hs]
        exact fun h ↦ by simp [h] at hs }

/-- The action of `stabilizer M a` is one-less preprimitive -/
theorem isMultiplyPreprimitive_ofStabilizer
    [IsPretransitive M α] {n : ℕ} {a : α} [IsMultiplyPreprimitive M α n.succ] :
    IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · rw [Nat.lt_one_iff] at h0
    rw [h0]
    apply is_zero_preprimitive
  exact {
    isMultiplyPretransitive := by
      rw [← ofStabilizer.isMultiplyPretransitive]
      exact IsMultiplyPreprimitive.isMultiplyPretransitive M α n.succ
    isPreprimitive_ofFixingSubgroup {s} hs  := by
      have : IsPreprimitive ↥(fixingSubgroup M (insert a (Subtype.val '' s)))
        ↥(ofFixingSubgroup M (insert a (Subtype.val '' s))) := by
        apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup M n.succ
        rw [Set.encard_insert_of_not_mem, Subtype.coe_injective.encard_image, hs, Nat.cast_succ]
        aesop
      exact IsPreprimitive.of_surjective
        (equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective a s).surjective }

/-- A pretransitive  action is n.succ-fold preprimitive  iff
  the action of stabilizers is n-fold preprimitive -/
theorem isMultiplyPreprimitive_succ_iff_ofStabilizer
    [IsPretransitive M α] {n : ℕ} (hn : 1 ≤ n) {a : α} :
    IsMultiplyPreprimitive M α n.succ ↔
      IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n := by
  constructor
  · apply isMultiplyPreprimitive_ofStabilizer
  · intro H
    exact {
      isMultiplyPretransitive := ofStabilizer.isMultiplyPretransitive.mpr H.isMultiplyPretransitive
      isPreprimitive_ofFixingSubgroup {s} hs := by
        have : ∃ b : α, b ∈ s := by
          rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
          intro h
          apply not_lt.mpr hn
          rw [h, Set.encard_empty, zero_add, ← Nat.cast_one, Nat.cast_inj, Nat.succ_inj'] at hs
          simp only [← hs, zero_lt_one]
        obtain ⟨b, hb⟩ := this
        obtain ⟨g, hg : g • b = a⟩ := exists_smul_eq M b a
        rw [isPreprimitive_ofFixingSubgroup_conj_iff (g := g)]
        set s' := g • s with hs'
        let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s'
        have hst : s' = insert a (Subtype.val '' t) := by
          ext x
          constructor
          · intro hxs
            by_cases hxa : x = a
            · simp [hxa]
            · exact Set.mem_insert_of_mem _
                ⟨⟨x, hxa⟩, by simp only [t, Set.mem_preimage]; exact hxs, rfl⟩
          · rw [Set.mem_insert_iff]
            rintro (⟨rfl⟩ | ⟨y, hy, rfl⟩)
            · simpa [s', ← hg]
            · simpa only using hy
        rw [hst, isPreprimitive_fixingSubgroup_insert_iff]
        apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
        apply ENat.add_left_injective_of_ne_top ENat.one_ne_top
        simp only
        rw [← Nat.cast_one, ← Nat.cast_add, ← hs]
        apply congr_arg₂ _ _ rfl
        rw [show s = g⁻¹ • s' from by ext; simp [hs'],
          ← Set.image_smul, (MulAction.injective g⁻¹).encard_image, hst]
        rw [Set.encard_insert_of_not_mem, Subtype.coe_injective.encard_image, ENat.coe_one]
        -- a ∉ Subtype.val '' t -- make it a general lemma ?
        rintro ⟨b, hb⟩; exact b.prop (by simp [hb]) }

/-- The fixator of a subset of cardinal d in an n-primitive action
  acts (n-d) primitively on the remaining (d ≤ n) -/
theorem ofFixingSubgroup.isMultiplyPreprimitive
    {m n : ℕ} [IsMultiplyPreprimitive M α n]
    {s : Set α} [Finite s]  (hs : s.ncard + m = n) :
    IsMultiplyPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m where
  isMultiplyPretransitive := by
    apply ofFixingSubgroup.isMultiplyPretransitive s hs
  isPreprimitive_ofFixingSubgroup {t} ht := by
    let t' : Set α := Subtype.val '' t
    have htt' : t = Subtype.val ⁻¹' t' :=
      (Set.preimage_image_eq _ Subtype.coe_injective).symm
    rw [htt']
    let f := map_ofFixingSubgroupUnion M s t'
    rw [← isPreprimitive_congr
      (fixingSubgroup_union_to_fixingSubgroup_fixingSubgroup_bijective M s t').surjective
      (map_ofFixingSubgroupUnion_bijective M s t') ]
    apply IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
    rw [Set.encard_union_eq _]
    · rw [Subtype.coe_injective.encard_image, add_assoc, ht,
        ← hs, Nat.cast_add, Set.Finite.cast_ncard_eq]
      exact Set.toFinite s
    · -- Disoint s (Subtype.val '' t) -- make it a general lemma?
      rw [Set.disjoint_iff]
      rintro a ⟨hbs, ⟨b, _, rfl⟩⟩; exact (b.prop hbs).elim

/-- n.succ-fold pretransitivity implies n-fold preprimitivity -/
theorem isMultiplyPreprimitive_of_isMultiplyPretransitive_succ {n : ℕ}
    (hα : ↑n.succ ≤ ENat.card α) [IsMultiplyPretransitive M α n.succ] :
    IsMultiplyPreprimitive M α n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  -- n = 0
  · rw [hn]
    exact is_zero_preprimitive M α
  -- n > 0
  · exact {
      isMultiplyPretransitive := isMultiplyPretransitive_of_le' (Nat.le_succ n) hα
      isPreprimitive_ofFixingSubgroup {s} hs := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
        -- rw [hm]
        apply isPreprimitive_of_is_two_pretransitive
        have hs' : s.encard = m := by
          simp [hm, add_comm 1] at hs
          exact ENat.add_left_injective_of_ne_top ENat.one_ne_top hs
        have : Finite s := Set.finite_of_encard_eq_coe hs'
        apply ofFixingSubgroup.isMultiplyPretransitive (M := M) s (n := n.succ)
        simp [Set.ncard, hs', hm, add_comm 1] }

/-- An n-fold preprimitive action is m-fold preprimitive for m ≤ n -/
theorem isMultiplyPreprimitive_of_le
    {n : ℕ} (hn : IsMultiplyPreprimitive M α n)
    {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ ENat.card α) :
    IsMultiplyPreprimitive M α m := by
  induction n with
  | zero => rw [Nat.eq_zero_of_le_zero hmn]; exact hn
  | succ n hrec =>
    rcases Nat.eq_or_lt_of_le hmn with hmn | hmn'
    · rw [hmn]; exact hn
    · apply hrec
        (isMultiplyPreprimitive_of_isMultiplyPretransitive_succ M α hα)
        (Nat.lt_succ_iff.mp hmn')
      · refine le_trans ?_ hα; rw [ENat.coe_le_coe]; exact Nat.le_succ n

variable {M α}

theorem isMultiplyPreprimitive_congr
    {N β : Type*} [Group N] [MulAction N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hf : Function.Bijective f) {n : ℕ}
    (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive N β n where
  isMultiplyPretransitive := IsPretransitive.of_embedding hf.surjective
  isPreprimitive_ofFixingSubgroup {t} ht := by
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
    have : IsPreprimitive (fixingSubgroup M s) (ofFixingSubgroup M s) :=
      IsMultiplyPreprimitive.isPreprimitive_ofFixingSubgroup _ n
        (by rw [← ht, ← hs', hf.injective.encard_image])
    exact IsPreprimitive.of_surjective (f := f') (φ := φ') hf'

end MulAction

