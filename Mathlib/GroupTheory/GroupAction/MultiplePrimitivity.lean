/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

! This file was ported from Lean 3 source module multiple_primitivity
-/

import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

open scoped BigOperators Pointwise Cardinal

-- open scoped Classical

section MultiplePrimitivity

namespace MulAction

variable (M α : Type _) [Group M] [MulAction M α]

/- example (e : PartENat) (h : e + 1 = 1) : e = 0 :=
  by
  rw [← PartENat.add_right_cancel_iff, zero_add]
  exact h
  rw [← Nat.cast_one]
  exact PartENat.natCast_ne_top 1

example (n : ℕ) (h : (n : PartENat) = 0) : n = 0 :=
  by
  rw [← Nat.cast_zero] at h
  rw [PartENat.natCast_inj] at h ; exact h

example (c : Cardinal) (n : ℕ) (h : c.toPartENat = n) : c = n :=
  by
  apply symm
  rw [← PartENat.coe_nat_eq_iff_eq]
  exact h.symm -/

/-- An action is n-fold preprimitive if it is n-fold pretransitive
and if the action of fixator of any (n-1) element subset on the remaining set
is not only pretransitive but also preprimitive. (Wielandt, §10)
-/
def IsMultiplyPreprimitive (n : ℕ) :=
  IsMultiplyPretransitive M α n ∧
    ∀ (s : Set α) (_ : s.encard + 1 = n),
      IsPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s)

example (p q: Prop) (h : q → False): q → p  := by
  exact fun a => (h a).elim
/-- Any action is 0-fold preprimitive -/
theorem isMultiplyPreprimitive_zero : IsMultiplyPreprimitive M α 0 := by
  constructor
  · apply MulAction.is_zero_pretransitive
  · intro s
    simp

/-- An action is preprimitive iff it is 1-preprimitive -/
theorem isPreprimitive_iff_is_one_preprimitive :
    IsPreprimitive M α ↔ IsMultiplyPreprimitive M α 1 := by
  constructor
  · intro h
    constructor
    · rw [← isPretransitive_iff_is_one_pretransitive]
      exact h.toIsPretransitive
    · intro s hs
      --  rw [Nat.cast_one] at hs
      simp only [Nat.cast_one] at hs
      suffices s = ∅ by
        rw [this]
        rw [isPreprimitive_of_bijective_map_iff
          (SubMulAction.of_fixingSubgroupEmpty_mapScalars_surjective M α)
          (SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective M α)]
        exact h
      rw [← Set.encard_eq_zero, ← Nat.cast_zero, ← WithTop.add_one_eq_coe_succ_iff]
      exact hs

  · rintro ⟨_, h1'⟩
    apply isPreprimitive_of_surjective_map
      (Function.Bijective.surjective
          (SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective M α))
    apply h1'
    simp only [Set.encard_empty, zero_add, Nat.cast_one]

/-- A multiply preprimitive action is multiply pretransitive -/
theorem IsMultiplyPreprimitive.toIsMultiplyPretransitive
    {n : ℕ} (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPretransitive M α n :=
  h.left

/-- A pretransitive  action is n.succ-fold preprimitive  iff
  the action of stabilizers is n-fold preprimitive -/
theorem stabilizer.isMultiplyPreprimitive
    {n : ℕ} (hn : 1 ≤ n) (h : IsPretransitive M α) {a : α} :
    -- (hα : (n.succ : cardinal) ≤ #α):
    IsMultiplyPreprimitive M α n.succ ↔
      IsMultiplyPreprimitive (stabilizer M a) (SubMulAction.ofStabilizer M a) n :=
  by
  let h_eq := h.exists_smul_eq
  constructor
  · intro hn
    cases' Nat.lt_or_ge n 1 with h0 h1
    · rw [Nat.lt_one_iff] at h0
      rw [h0]
      apply isMultiplyPreprimitive_zero
    constructor
    -- n-pretransitive
    exact (stabilizer.isMultiplyPretransitive M α h).mp hn.left
    -- multiple preprimitivity property
    intro s hs
    apply isPreprimitive_of_surjective_map
        (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective M a s).surjective
    apply hn.right
    rw [Set.encard_insert_of_not_mem, Subtype.coe_injective.encard_image, hs, Nat.cast_succ]
    · intro ha
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at ha
      obtain ⟨b, _⟩ := ha
      apply b
      simp only [Set.mem_singleton_iff]

  · intro hn_0
    constructor
    · rw [stabilizer.isMultiplyPretransitive M α h]
      exact hn_0.left
    · suffices
        ∀ (s : Set α) (_ : s.encard + 1 = n.succ) (_ : a ∈ s),
          IsPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) by
        intro s hs
        have : ∃ b : α, b ∈ s := by
          rw [← Set.nonempty_def, Set.nonempty_iff_ne_empty]
          intro h
          apply not_lt.mpr hn
          rw [h, Set.encard_empty, zero_add, ← Nat.cast_one, Nat.cast_inj, Nat.succ_inj'] at hs
          simp only [← hs, zero_lt_one]
        obtain ⟨b, hb⟩ := this
        obtain ⟨g, hg : g • b = a⟩ := h_eq b a
        apply isPreprimitive_of_surjective_map
          (SubMulAction.conjMap_ofFixingSubgroup_bijective M (inv_smul_smul g s)).surjective
        refine this (g • s) ?_ ⟨b, hb, hg⟩
        rw [smul_set_encard_eq, hs]

      intro s hs has
      rw [WithTop.add_one_eq_coe_succ_iff] at hs
      let t : Set (SubMulAction.ofStabilizer M a) := Subtype.val ⁻¹' s
      have hst : s = insert a (Subtype.val '' t) := by
        ext x
        constructor
        · intro hxs
          by_cases hxa : x = a
          rw [hxa]; apply Set.mem_insert
          apply Set.mem_insert_of_mem
          use ⟨x, ?_⟩
          refine And.intro ?_ rfl
          · simp only [t, Set.mem_preimage]
            exact hxs
          exact hxa
        · intro hxat
          cases' Set.mem_insert_iff.mp hxat with hxa hxt
          rw [hxa]; exact has
          obtain ⟨y, hy, rfl⟩ := hxt
          simpa only using hy
      rw [hst]
      rw [isPreprimitive_of_bijective_map_iff
          (SubMulAction.scalarMap_ofFixingSubgroupOfStabilizer_bijective M a t).surjective
          (SubMulAction.equivariantMap_ofFixingSubgroup_to_ofStabilizer_bijective M a t)]
      · apply hn_0.right t
        rw [← hs, hst, Set.encard_insert_of_not_mem, Subtype.coe_injective.encard_image]
        rintro ⟨x, hx⟩
        apply x.prop; rw [hx.right]; simp only [Set.mem_singleton]


/- lemma is_multiply_preprimitive_of_subgroup {H : subgroup M}
  {n : ℕ} (hn : n ≥ 1) (hH : is_multiply_preprimitive H α n) :
  is_multiply_preprimitive M α n :=
begin
  let j : mul_action_bihom H α M α :=
  { to_fun := id,
    to_monoid_hom := subgroup_class.subtype H,
    map_smul' := λ m x, rfl },

  split,
  apply is_pretransitive_of_subgroup,
  exact hH.left,

  intros s hs,
  apply is_preprimitive.mk,
  rw is_pretransitive_iff_is_one_pretransitive,
  have hn1 : n = (n - 1) + 1,
  by rw ← (nat.sub_eq_iff_eq_add hn),

  suffices : #s = ↑(n - 1) ∧ 1 = n - (n-1),
  { rw this.right,
    apply remaining_transitivity M α (n-1) s this.left,
    apply is_pretransitive_of_subgroup,
    exact hH.left, },
  split,
  { apply cardinal.add_cancel,
    swap, exact 1,
    rw [nat.cast_one, hs],
    suffices : n = (n - 1) + 1,
    conv_lhs { rw this },
    simp only [nat.cast_add, nat.cast_one],
    exact hn1 },
  suffices : n ≥ (n - 1),
  rw add_comm at hn1, apply symm,
  exact (nat.sub_eq_iff_eq_add this).mpr hn1,
  exact nat.sub_le n 1,

  intros B hB,
  apply  (hH.right s hs).has_trivial_blocks,
  rw is_block.mk_mem at hB ⊢,
  rintros ⟨⟨g, hgH⟩, hgs⟩ ⟨a, ha⟩ haB hga,
  suffices : (⟨g, _⟩ : fixing_subgroup M s) • B = B,
  exact this,
  apply hB ⟨g, begin simpa only using hgs end⟩ ⟨a, begin simpa only using ha end⟩,
  simpa only using haB,
  simpa only using hga,
end
 -/
/-- The fixator of a subset of cardinal d in an n-primitive action
  acts (n-d) primitively on the remaining (d ≤ n)-/
theorem remaining_primitivity
    {m n : ℕ} {s : Set α} [Finite s] (hs : n = m + s.ncard)
    (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive (fixingSubgroup M s) (SubMulAction.ofFixingSubgroup M s) m :=
  by
  constructor
  · apply remaining_transitivity M α s h.left hs
  · intro t ht
    let t' : Set α := Subtype.val '' t
    have htt' : t = Subtype.val ⁻¹' t' := by
      apply symm
      apply Set.preimage_image_eq
      exact Subtype.coe_injective
    rw [htt']
    apply isPreprimitive_of_surjective_map
        (SubMulAction.OfFixingSubgroupUnion.map_bijective M s t').surjective
    apply h.right
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
  cases' Nat.eq_zero_or_pos n with hn hn
  -- n = 0
  · rw [hn]
    apply isMultiplyPreprimitive_zero
  -- n > 0
  constructor
  apply isMultiplyPretransitive_of_higher M α h
  exact Nat.le_succ n
  exact hα
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [hm]
  intro s hs
  apply IsMultiplyPretransitive.isPreprimitive_of_two
  rw [add_comm _ m, Nat.cast_add, ← Nat.cast_one, WithTop.add_eq_add_iff] at hs
  have : Finite s := by rw [Set.finite_coe_iff]; exact Set.finite_of_encard_eq_coe hs
  apply remaining_transitivity M α s h
  unfold Set.ncard
  rw [hs, hm, ENat.toNat_coe, ← Nat.succ_add]

/-- An n-fold preprimitive action is m-fold preprimitive for m ≤ n -/
theorem isMultiplyPreprimitive_of_higher
    {n : ℕ} {m : ℕ} (hmn : m ≤ n) (hα : ↑n ≤ ENat.card α)
    (hn : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive M α m := by
  -- induction on n
  induction' n with n hrec
  -- n = 0 : implies m = 0
  · simp only [Nat.zero_eq, nonpos_iff_eq_zero] at hmn
    rw [hmn]
    apply isMultiplyPreprimitive_zero
  -- induction step
  · cases' Nat.eq_or_lt_of_le hmn with hmn hmn'
    -- m = n + 1 = this is hn
    · rw [hmn]; exact hn
    -- m < n + 1 : use induction hypothesis
    · apply hrec (Nat.lt_succ_iff.mp hmn')
      refine le_trans ?_ hα; rw [ENat.coe_le_coe]; exact Nat.le_succ n
      -- get one step by transitivity
      apply isMultiplyPreprimitive_of_multiply_pretransitive_succ M α hα hn.left

variable {M α}

theorem isMultiplyPreprimitive_of_bijective_map
    {N β : Type _} [Group N] [MulAction N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hf : Function.Bijective f) {n : ℕ}
    (h : IsMultiplyPreprimitive M α n) :
    IsMultiplyPreprimitive N β n := by
  constructor
  apply isMultiplyPretransitive_of_surjective_map hf.surjective h.left
  intro t ht
  let s := f ⁻¹' t
  have hs' : f '' s = t := Set.image_preimage_eq t hf.surjective
  let φ' : fixingSubgroup M s → fixingSubgroup N t := fun ⟨m, hm⟩ =>
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
    · simp only [f']
      apply Subtype.coe_injective
      exact hx
    · intro h
      apply hy
      rw [← hs']
      exact ⟨x, h, hx⟩
  refine isPreprimitive_of_surjective_map hf' (h.right s ?_)
  rw [← ht, ← hs', hf.injective.encard_image]

end MulAction

end MultiplePrimitivity

#
