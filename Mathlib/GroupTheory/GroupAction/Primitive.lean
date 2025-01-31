/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Setoid.Partition
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Primitive actions

## Definitions

- `IsPreprimitive G X`
  A structure that says that the action of a type `G` on a type `X`
  (defined by an instance `SMul G X`) is *preprimitive*,
  namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
  (The pretransitivity assumption is essentially trivial,
  because orbits are blocks, unless the action itself is trivial.)

  The notion which is introduced in classical books on group theory
  is restricted to group actions.
  In fact, it may be irrelevant if the action is degenerate,
  when “trivial blocks” might not be blocks.
  Moreover, the classical notion is *primitive*,
  which assumes moreover that `X` is not empty.

- `IsQuasipreprimitive G X`
  A structure that says that the action of the group `G` on the type `X` is *quasipreprimitive*,
  namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity
  under equivariant maps, for images and preimages.

## Relation with stabilizers

- `isPreprimitive_of_block_order`
  relates primitivity and the fact that the inclusion
  order on blocks containing is simple.

- `maximal_stabilizer_iff_preprimitive`
  An action is preprimitive iff the stabilizers of points are maximal subgroups.

## Relation with normal subgroups

- `IsPreprimitive.isQuasipreprimitive`
  Preprimitive actions are quasipreprimitive

## Particular results for actions on finite types

- `MulAction.isPreprimitive_of_primeCard` :
  A pretransitive action on a finite type of prime cardinal is preprimitive.

- `IsPreprimitive.of_card_lt`
  Given an equivariant map from a preprimitive action,
  if the image is at least twice the codomain, then the codomain is preprimitive.

- `Rudio` : Theorem of Rudio :
  Given a preprimitive action of a group `G` on `X`, a finite `A : set X`
  and two points, find a translate of `A` that contains one of them and not the other one.
  The proof relies on `IsBlock.of_subset` that itself requires finiteness of `A`,
  but I don't know whether the theorem does…

-/

open Pointwise

namespace MulAction

section Primitive

variable (G : Type*) (X : Type*)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An additive action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
class _root_.AddAction.IsPreprimitive [VAdd G X] extends AddAction.IsPretransitive G X : Prop where
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
  has_trivial_blocks' : ∀ {B : Set X}, AddAction.IsBlock G B → AddAction.IsTrivialBlock B

/-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
@[to_additive]
class IsPreprimitive [SMul G X] extends IsPretransitive G X : Prop where
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
  has_trivial_blocks' : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B

/-- An additive action of an additive group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
class _root_.AddAction.IsQuasipreprimitive
    [AddGroup G] [AddAction G X] extends AddAction.IsPretransitive G X : Prop where
  pretransitive_of_normal :
    ∀ {N : AddSubgroup G} (_ : N.Normal), AddAction.fixedPoints N X ≠ ⊤ →
      AddAction.IsPretransitive N X

/-- A `mul_action` of a group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
@[to_additive]
class IsQuasipreprimitive [Group G] [MulAction G X] extends IsPretransitive G X : Prop where
  pretransitive_of_normal :
    ∀ {N : Subgroup G} (_ : N.Normal), fixedPoints N X ≠ ⊤ → IsPretransitive N X

variable {G X}

namespace IsPreprimitive

@[to_additive]
theorem has_trivial_blocks [SMul G X] (h : IsPreprimitive G X) {B : Set X}
    (hB : IsBlock G B) : B.Subsingleton ∨ B = ⊤ := by apply h.has_trivial_blocks'; exact hB

@[to_additive]
theorem on_subsingleton [SMul G X] [Nonempty G] [Subsingleton X] :
    IsPreprimitive G X := by
  have : IsPretransitive G X := by
    apply IsPretransitive.mk
    intro x y
    use Classical.arbitrary G
    rw [eq_iff_true_of_subsingleton]
    trivial
  apply IsPreprimitive.mk
  intro B _
  left
  exact Set.subsingleton_of_subsingleton

variable [Group G] [MulAction G X]

open scoped BigOperators Pointwise

/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/
@[to_additive
"If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition)"]
theorem mk_mem_of_pretransitive [htGX : IsPretransitive G X] (a : X)
    (H : ∀ (B : Set X) (_ : a ∈ B) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  apply IsPreprimitive.mk
  intro B hB
  cases Set.eq_empty_or_nonempty B with
  | inl h => apply Or.intro_left; rw [h]; exact Set.subsingleton_empty
  | inr h =>
    obtain ⟨b, hb⟩ := h
    obtain ⟨g, hg⟩ := exists_smul_eq G b a
    rw [← IsTrivialBlock.smul_iff g]
    apply H (g • B) _ (hB.translate g)
    rw [← hg]
    use b

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) (based condition) -/
@[to_additive
  "If the action is not trivial, then the trivial blocks condition implies preprimitivity
  (pretransitivity is automatic) (based condition)"]
theorem mk_mem {a : X} (ha : a ∉ fixedPoints G X)
    (H : ∀ (B : Set X) (_ : a ∈ B) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  have : IsPretransitive G X := by
    rw [isPretransitive_iff_base a]
    cases' H (orbit G a) (mem_orbit_self a) (IsBlock.orbit a) with H H
    · exfalso; apply ha
      rw [Set.subsingleton_iff_singleton (mem_orbit_self a)] at H
      simp only [mem_fixedPoints]
      intro g
      rw [← Set.mem_singleton_iff]; rw [← H]
      exact mem_orbit a g
    · intro x; rw [← MulAction.mem_orbit_iff, H]; exact Set.mem_univ x
  apply IsPreprimitive.mk
  intro B hB
  cases Set.eq_empty_or_nonempty B with
  | inl h => left; rw [h]; exact Set.subsingleton_empty
  | inr h =>
    obtain ⟨b, hb⟩ := h
    obtain ⟨g, hg⟩ := exists_smul_eq G b a
    rw [← IsTrivialBlock.smul_iff g]
    exact H (g • B) ⟨b, hb, hg⟩ (hB.translate g)

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
    (pretransitivity is automatic) -/
@[to_additive
  "If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic)"]
theorem mk' (Hnt : fixedPoints G X ≠ ⊤)
    (H : ∀ (B : Set X) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem] at Hnt
  obtain ⟨a, ha⟩ := Hnt
  exact mk_mem ha (fun B _ ↦ H B)

end IsPreprimitive

section EquivariantMap

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M →* N} {f : α →ₑ[φ] β}

@[to_additive]
theorem IsPreprimitive.of_surjective
    (hf : Function.Surjective f) (h : IsPreprimitive M α) :
    IsPreprimitive N β := by
  have : IsPretransitive N β := h.toIsPretransitive.of_surjective_map hf
  apply IsPreprimitive.mk
  · intro B hB
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    apply h.has_trivial_blocks
    exact IsBlock.preimage f hB

@[to_additive]
theorem IsPreprimitive.iff_of_bijective
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β := by
  constructor
  · apply IsPreprimitive.of_surjective hf.surjective
  · intro hN
    haveI := (isPretransitive_congr hφ hf).mpr hN.toIsPretransitive
    apply IsPreprimitive.mk
    · intro B hB
      rw [← Set.preimage_image_eq B hf.injective]
      exact IsTrivialBlock.preimage hf.injective
        (hN.has_trivial_blocks (hB.image f hφ hf.injective))

end EquivariantMap

section Stabilizer

variable (G : Type*) [Group G] {X : Type*} [MulAction G X]

open scoped BigOperators Pointwise

/-- A pretransitive action on a nontrivial type is preprimitive iff
    the set of blocks containing a given element is a simple order -/
@[to_additive
  "A pretransitive action on a nontrivial type is preprimitive iff
  the set of blocks containing a given element is a simple order"]
theorem isPreprimitive_iff_isSimpleOrder_blocks
    [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsPreprimitive G X ↔ IsSimpleOrder (BlockMem G a) := by
  constructor
  · intro hGX'; apply IsSimpleOrder.mk
    rintro ⟨B, haB, hB⟩
    simp only [← Subtype.coe_inj, Subtype.coe_mk]
    cases hGX'.has_trivial_blocks hB with
    | inl h => simp [BlockMem.coe_bot, h.eq_singleton_of_mem haB]
    | inr h => simp [BlockMem.coe_top, h]
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.mk_mem_of_pretransitive a
    intro B haB hB
    cases' h_bot_or_top ⟨B, haB, hB⟩ with hB' hB' <;>
      simp only [← Subtype.coe_inj, Subtype.coe_mk] at hB'
    · left; simp [hB']
    · right; simp [hB']

/-- A pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
@[to_additive
  "A pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5)"]
theorem maximal_stabilizer_iff_preprimitive
    [htGX : IsPretransitive G X] [hnX : Nontrivial X] (a : X) :
    IsCoatom (stabilizer G a) ↔ IsPreprimitive G X := by
  rw [isPreprimitive_iff_isSimpleOrder_blocks G a,
    ← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a), OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
@[to_additive "In a preprimitive action, stabilizers are maximal subgroups."]
theorem hasMaximalStabilizersOfPreprimitive
    [Nontrivial X] (hpGX : IsPreprimitive G X) (a : X) :
    IsCoatom (stabilizer G a) := by
  haveI : IsPretransitive G X := hpGX.toIsPretransitive
  rw [maximal_stabilizer_iff_preprimitive]
  exact hpGX

end Stabilizer

section Normal

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]

/-- In a preprimitive action,
  any normal subgroup that acts nontrivially is pretransitive
  (Wielandt, th. 7.1)-/
@[to_additive "In a preprimitive additive action,
  any normal subgroup that acts nontrivially is pretransitive (Wielandt, th. 7.1)"]
theorem IsPreprimitive.isQuasipreprimitive (hGX : IsPreprimitive M α) :
    IsQuasipreprimitive M α := by
  apply IsQuasipreprimitive.mk
  intro N hN hNX
  rw [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem] at hNX
  obtain ⟨a, ha⟩ := hNX
  rw [isPretransitive_iff_orbit_eq_top a]
  apply Or.resolve_left (hGX.has_trivial_blocks (IsBlock.orbit_of_normal a))
  intro h
  apply ha
  simp only [mem_fixedPoints]
  intro n
  rw [← Set.mem_singleton_iff]
  suffices orbit N a = {a} by rw [← this]; use n
  ext b
  rw [Set.Subsingleton.eq_singleton_of_mem h (MulAction.mem_orbit_self a)]

end Normal

section Finite

namespace IsPreprimitive

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]

open scoped BigOperators Pointwise

/-- A pretransitive action on a set of prime order is preprimitive -/
@[to_additive "A pretransitive action on a set of prime order is preprimitive"]
theorem of_prime_card [hGX : IsPretransitive M α] (hp : Nat.Prime (Nat.card α)) :
    IsPreprimitive M α := by
  classical
  apply IsPreprimitive.mk
  intro B hB
  cases' Set.subsingleton_or_nontrivial B with hB' hB'
  · apply Or.intro_left
    exact hB'
  · apply Or.intro_right
    have : Finite α := (Nat.card_ne_zero.mp (Nat.Prime.ne_zero hp)).2
    cases (Nat.dvd_prime hp).mp (hB.ncard_dvd_card hB'.nonempty) with
    | inl h =>
      exfalso
      exact ((Set.one_lt_ncard B.toFinite).mpr hB').ne h.symm
    | inr h =>
      rwa [Set.eq_univ_iff_ncard]

variable {φ : M → N} {f : α →ₑ[φ] β}

/-- The target of an equivariant map of large image is preprimitive if the source is -/
@[to_additive "The target of an equivariant map of large image is preprimitive if the source is"]
theorem of_card_lt
    [Finite β] [htβ : IsPretransitive N β] (hM : IsPreprimitive M α)
    (hf' : Nat.card β < 2 * (Set.range f).ncard) :
    IsPreprimitive N β :=  by
  classical
  apply IsPreprimitive.mk
  intro B hB
  cases' B.eq_empty_or_nonempty with hB' hB'
  · left
    rw [hB']
    apply Set.subsingleton_empty
  rw [IsTrivialBlock, or_iff_not_imp_right]
  intro hB_ne_top
  -- we need Set.Subsingleton B ↔ Set.ncard B ≤ 1
  suffices Set.ncard B < 2 by
    rw [Nat.lt_succ, Set.ncard_le_one_iff] at this
    exact fun ⦃x⦄ x_1 ⦃y⦄ ↦ this x_1
  -- We reduce to proving that (Set.range f).ncard ≤ (orbit N B).ncard
  apply lt_of_mul_lt_mul_right (lt_of_le_of_lt _ hf') (Nat.zero_le _)
  simp only [← Nat.card_eq_fintype_card, ← hB.ncard_block_mul_ncard_orbit_eq hB']
  apply Nat.mul_le_mul_left
  -- We reduce to proving that (Set.range f ∩ g • B).ncard ≤ 1 for every g
  rw [(hB.isBlockSystem hB').left.ncard_eq_finsum]
  rw [finsum_eq_finset_sum_of_support_subset]
  · apply le_trans (Finset.sum_le_card_nsmul _ _ 1 _)
    · simp only [smul_eq_mul, mul_one]
      conv_rhs => rw [Set.ncard_coe]
      apply le_of_eq
      rw [← Set.ncard_eq_toFinset_card]
    · rintro ⟨x, ⟨g, hg⟩⟩ _
      simp only [← hg]
      suffices Set.Subsingleton (Set.range f ∩ g • B) by
        rw [Set.ncard_le_one_iff]
        exact fun {a b} a_1 a_2 ↦ this a_1 a_2
    -- It suffices to prove that the preimage is subsingleton
      rw [← Set.image_preimage_eq_range_inter]
      apply Set.Subsingleton.image
    -- Since the action of M on α is primitive, it suffices to prove that
    -- the preimage is a block which is not ⊤
      apply Or.resolve_right (hM.has_trivial_blocks ((hB.translate g).preimage f))
      intro h
      simp only [Set.top_eq_univ, Set.preimage_eq_univ_iff] at h
    -- We will prove that B is large, which will contradict the assumption that it is not ⊤
      apply hB_ne_top
      apply hB.eq_univ_of_card_lt
    -- It remains to show that Nat.card β < Set.ncard B * 2
      apply lt_of_lt_of_le hf'
      rw [mul_comm, mul_le_mul_right Nat.succ_pos']
      apply le_trans (Set.ncard_le_ncard h) (Set.ncard_image_le B.toFinite)
  simp only [Set.Finite.coe_toFinset, Set.subset_univ]

/-- Theorem of Rudio (Wielandt, 1964, Th. 8.1) -/
@[to_additive "Theorem of Rudio (Wielandt, 1964, Th. 8.1)"]
theorem rudio (hpGX : IsPreprimitive M α)
    {A : Set α} (hfA : A.Finite) (hA : A.Nonempty) (hA' : A ≠ ⊤)
    {a b : α} (h : a ≠ b) :
    ∃ g : M, a ∈ g • A ∧ b ∉ g • A := by
  let B := ⋂ (g : M) (_ : a ∈ g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  -- B is a block hence is a trivial block
  cases' hpGX.has_trivial_blocks (IsBlock.of_subset a hfA) with hyp hyp
  · -- B.subsingleton
    apply Set.Subsingleton.eq_singleton_of_mem hyp
    rw [Set.mem_iInter]; intro g; simp only [Set.mem_iInter, imp_self]
  · -- B = ⊤ : contradiction
    change B = ⊤ at hyp
    exfalso; apply hA'
    suffices ∃ g : M, a ∈ g • A by
      obtain ⟨g, hg⟩ := this
      have : B ≤ g • A := Set.biInter_subset_of_mem hg
      rw [hyp, top_le_iff, ← eq_inv_smul_iff] at this
      rw [this, Set.top_eq_univ, Set.smul_set_univ]
    -- ∃ (g : M), a ∈ g • A
    obtain ⟨x, hx⟩ := hA
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M x a
    use g; use x

end IsPreprimitive

end Finite

end Primitive

end MulAction
