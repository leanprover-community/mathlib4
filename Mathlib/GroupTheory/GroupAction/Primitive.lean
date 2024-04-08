/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/
/-
import Jordan.Mathlib.Stabilizer
import Jordan.Mathlib.Pretransitive
import Jordan.Mathlib.Set
import Jordan.Mathlib.Partitions
import Jordan.SubMulActions
import Jordan.Mathlib.Commutators
-/

-- import Jordan.EquivariantMap
import Mathlib.GroupTheory.MaximalSubgroups
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Transitive

import Mathlib.Data.Nat.Prime

/-
import Mathlib.Data.Setoid.Partition
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Subgroup.Pointwise
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Abelianization
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Set.Card
-/

/-!
# Primitive actions

## Definitions

- `IsPreprimitive G X`
a structure that says that the action of a type `G`
on a type `X` (defined by an instance `SMul G X`) is *preprimitive*,
namely, it is pretransitive and the only blocks are ⊤ and subsingletons.
(The pretransitivity assumption is essentially trivial,
because orbits are blocks, unless the action itself is trivial.)

The notion which is introduced in classical books on group theory
is restricted to `mul_action` of groups.
In fact, it may be irrelevant if the action is degenerate,
when “trivial blocks” might not be blocks.
Moreover, the classical notion is *primitive*,
which assumes moreover that `X` is not empty.

- `IsQuasipreprimitive G X`
a structure that says that the `mul_action`
of the group `G` on the type `X` is *quasipreprimitive*,
namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity under equivariant maps, for images and preimages.

## Relation with stabilizers

- `isPreprimitive_of_block_order`
relates primitivity and the fact that the inclusion
order on blocks containing is simple.

- `maximal_stabilizer_iff_preprimitive`
an action is preprimitive iff the stabilizers of points are maximal subgroups.

## Relation with normal subgroups

- `IsPreprimitive.isQuasipreprimitive`
preprimitive actions are quasipreprimitive

## Particular results for actions on finite types

- `isPreprimitive_of_primeCard` :
a pretransitive action on a finite type of prime cardinal is preprimitive

- `isPreprimitive_of_large_image`
Given an equivariant map from a preprimitive action,
if the image is at least twice the codomain, then the codomain is preprimitive

- `Rudio`
Theorem of Rudio :
Given a preprimitive action of a group `G` on `X`, a finite `A : set X`
and two points, find a translate of `A` that contains one of them
and not the other one.
The proof relies on `is_block.of_subset` that itself requires finiteness of `A`,
but I don't know whether the theorem does…

-/

open MulAction

section Primitive

variable (G : Type _) (X : Type _)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
class IsPreprimitive [SMul G X] extends IsPretransitive G X : Prop where
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
  has_trivial_blocks' : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B
#align is_preprimitive IsPreprimitive

/-- A `mul_action` of a group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
class IsQuasipreprimitive [Group G] [MulAction G X] extends IsPretransitive G X : Prop where
/-- A `mul_action` of a group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
  pretransitive_of_normal :
    ∀ {N : Subgroup G} (_ : N.Normal), fixedPoints N X ≠ ⊤ → MulAction.IsPretransitive N X
#align is_quasipreprimitive IsQuasipreprimitive

variable {G X}

namespace IsPreprimitive

theorem has_trivial_blocks [SMul G X] (h : IsPreprimitive G X) {B : Set X}
    (hB : IsBlock G B) : B.Subsingleton ∨ B = ⊤ := by apply h.has_trivial_blocks'; exact hB

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

theorem mk_mem' [htGX : IsPretransitive G X] (a : X)
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
    refine' H (g • B) _ (IsBlock_of_block g hB)
    use b

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) (based condition) -/
theorem mk_mem {a : X} (ha : a ∉ fixedPoints G X)
    (H : ∀ (B : Set X) (_ : a ∈ B) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  have : IsPretransitive G X := by
    rw [IsPretransitive.mk_base_iff a]
    cases' H (orbit G a) (mem_orbit_self a) (IsBlock_of_orbit a) with H H
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
    refine' H (g • B) _ (IsBlock_of_block g hB)
    use b
#align is_preprimitive.mk_mem' IsPreprimitive.mk_mem'

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/
theorem mk' (Hnt : fixedPoints G X ≠ ⊤)
    (H : ∀ (B : Set X) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem] at Hnt
  obtain ⟨a, ha⟩ := Hnt
  exact mk_mem ha (fun B _ ↦ H B)

end IsPreprimitive

section EquivariantMap

section Monoid

variable {M : Type _} [Monoid M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Monoid N] [MulAction N β]

theorem isTrivialBlock_of_surjective_map {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f)
    {B : Set α} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f '' B) := by
  cases' hB with hB hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.top_eq_univ, Set.image_univ, Set.range_iff_surjective]
    exact hf

theorem isTrivialBlock_of_injective_map {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Injective f)
    {B : Set β} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f ⁻¹' B) := by
  cases' hB with hB hB
  apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  apply Or.intro_right; simp only [hB, Set.top_eq_univ]; apply Set.preimage_univ
#align is_trivial_block_of_injective_map isTrivialBlock_of_injective_map

end Monoid

section Group
variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Group N] [MulAction N β]

-- TODO : generalize to φ : M → N
theorem isPreprimitive_of_surjective_map {φ : M →* N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f)
    (h : IsPreprimitive M α) : IsPreprimitive N β := by
  have : IsPretransitive N β := h.toIsPretransitive.of_surjective_map hf
  apply IsPreprimitive.mk
  · intro B hB
    rw [← Set.image_preimage_eq B hf]
    apply isTrivialBlock_of_surjective_map hf
    -- make has_trivial_blocks return `IsTrivialBlock`?
    apply h.has_trivial_blocks
    exact IsBlock_preimage f hB

-- TODO : generalize to φ : M → N
theorem IsPreprimitive.iff_of_bijective_map {φ : M →* N} {f : α →ₑ[φ] β}
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β := by
  constructor
  apply isPreprimitive_of_surjective_map hf.surjective
  intro hN
  haveI := (IsPretransitive.iff_of_bijective_map hφ hf).mpr hN.toIsPretransitive
  apply IsPreprimitive.mk
  · intro B hB
    rw [← Set.preimage_image_eq B hf.injective]
    apply isTrivialBlock_of_injective_map hf.injective
    apply hN.has_trivial_blocks
    apply IsBlock_image f hφ hf.injective
    exact hB

end Group

end EquivariantMap

section Stabilizer

variable (G : Type _) [Group G] {X : Type _} [MulAction G X]

open scoped BigOperators Pointwise

instance Block.boundedOrderOfMem (a : X) :
    BoundedOrder { B : Set X // a ∈ B ∧ IsBlock G B } where
  top := ⟨⊤, by rw [Set.top_eq_univ]; apply Set.mem_univ, top_IsBlock X⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Set.top_eq_univ, Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, singleton_IsBlock a⟩
  bot_le := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.singleton_subset_iff]
    exact ha

theorem Block.boundedOrderOfMem.top_eq (a : X) :
    ((Block.boundedOrderOfMem G a).top : Set X) = ⊤ :=
  rfl

theorem Block.boundedOrderOfMem.bot_eq (a : X) :
    ((Block.boundedOrderOfMem G a).bot : Set X) = {a} :=
  rfl

theorem Block.mem_is_nontrivial_order_of_nontrivial [Nontrivial X] (a : X) :
    Nontrivial { B : Set X // a ∈ B ∧ IsBlock G B } := by
  rw [nontrivial_iff]
  use (Block.boundedOrderOfMem G a).bot
  use (Block.boundedOrderOfMem G a).top
  intro h
  rw [← Subtype.coe_inj] at h
  simp only [Block.boundedOrderOfMem.top_eq, Block.boundedOrderOfMem.bot_eq] at h
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff, h, Set.top_eq_univ]
  apply Set.mem_univ

/-- A pretransitive action on a nontrivial type is preprimitive iff
the set of blocks containing a given element is a simple order -/
theorem isPreprimitive_iff_isSimpleOrder_blocks
    [htGX : IsPretransitive G X] [Nontrivial X] (a : X) :
    IsPreprimitive G X ↔ IsSimpleOrder { B : Set X // a ∈ B ∧ IsBlock G B } := by
  haveI : Nontrivial { B : Set X // a ∈ B ∧ IsBlock G B } :=
    Block.mem_is_nontrivial_order_of_nontrivial G a
  constructor
  · intro hGX'; apply IsSimpleOrder.mk
    rintro ⟨B, haB, hB⟩
    simp only [← Subtype.coe_inj, Subtype.coe_mk]
    cases hGX'.has_trivial_blocks hB with
    | inl h =>
      apply Or.intro_left
      change B = ↑(Block.boundedOrderOfMem G a).bot
      rw [Block.boundedOrderOfMem.bot_eq]
      exact Set.Subsingleton.eq_singleton_of_mem h haB
    | inr h =>
      apply Or.intro_right
      change B = ↑(Block.boundedOrderOfMem G a).top
      exact h
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.mk_mem' a
    intro B haB hB
    cases' h_bot_or_top ⟨B, haB, hB⟩ with hB' hB' <;>
      simp only [← Subtype.coe_inj, Subtype.coe_mk] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · right; rw [hB']; rfl

/-- A pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
theorem maximal_stabilizer_iff_preprimitive
    [htGX : IsPretransitive G X] [hnX : Nontrivial X] (a : X) :
    (stabilizer G a).IsMaximal ↔ IsPreprimitive G X := by
  rw [isPreprimitive_iff_isSimpleOrder_blocks G a, Subgroup.isMaximal_def, ← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (stabilizerBlockEquiv G a), OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
theorem hasMaximalStabilizersOfPreprimitive
    [hnX : Nontrivial X] (hpGX : IsPreprimitive G X) (a : X) :
    (stabilizer G a).IsMaximal := by
  haveI : IsPretransitive G X := hpGX.toIsPretransitive
  rw [maximal_stabilizer_iff_preprimitive]
  exact hpGX

end Stabilizer

section Normal

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

/-- If a subgroup acts nontrivially, then the type is nontrivial -/
theorem isnontrivial_of_nontrivial_action {N : Subgroup M} (h : fixedPoints N α ≠ ⊤) :
    Nontrivial α := by
  apply Or.resolve_left (subsingleton_or_nontrivial α)
  intro hα
  apply h
  rw [eq_top_iff]
  intro x hx
  rw [mem_fixedPoints]
  intro g
  rw [subsingleton_iff] at hα
  apply hα

/-- In a preprimitive action,
  any normal subgroup that acts nontrivially is pretransitive
  (Wielandt, th. 7.1)-/
theorem IsPreprimitive.isQuasipreprimitive (hGX : IsPreprimitive M α) :
    IsQuasipreprimitive M α := by
  apply IsQuasipreprimitive.mk
  intro N hN hNX
  rw [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem] at hNX
  obtain ⟨a, ha⟩ := hNX
  rw [IsPretransitive.iff_orbit_eq_top a]
  apply Or.resolve_left (hGX.has_trivial_blocks (orbit.IsBlock_of_normal hN a))
  intro h
  apply ha; simp only [mem_fixedPoints]; intro n
  rw [← Set.mem_singleton_iff]
  suffices orbit N a = {a} by rw [← this]; use n
  · ext b
    rw [Set.Subsingleton.eq_singleton_of_mem h (MulAction.mem_orbit_self a)]

end Normal

section Finite

variable {M : Type _} [Group M] {α : Type _} [MulAction M α]

variable {N β : Type _} [Group N] [MulAction N β]

open scoped BigOperators Pointwise

/-- A pretransitive action on a set of prime order is preprimitive -/
theorem isPreprimitive_of_prime [Finite α] [hGX : IsPretransitive M α]
    (hp : Nat.Prime (Nat.card α)) :
    IsPreprimitive M α := by
  classical
  apply IsPreprimitive.mk
  intro B hB
  cases' Set.subsingleton_or_nontrivial B with hB' hB'
  · apply Or.intro_left
    exact hB'
  · apply Or.intro_right
    suffices Set.ncard B = 1 ∨ Set.ncard B = Nat.card α by
      cases' this with h h
      · exfalso
        rw [Set.ncard_eq_one] at h
        obtain ⟨a, rfl⟩ := h
        exact Set.not_nontrivial_singleton hB'
      · -- make a lemma out of this?
        simp only [Set.top_eq_univ, Set.subset_univ]
        apply Set.eq_of_subset_of_ncard_le
        apply Set.subset_univ
        rw [h, Set.ncard_univ]
        exact Set.finite_univ
    rw [← Nat.dvd_prime hp]
    apply ncard_of_block_divides hB
    exact Set.Nontrivial.nonempty hB'

section

open scoped Classical


example (α : Type*) [Fintype α] (s : Set α) [Fintype s]:
  Nat.card s = s.toFinset.card := by
  simp only [Nat.card_eq_fintype_card, Set.toFinset_card]



end

/-

/-- The target of an equivariant map of large image is preprimitive if the source is -/
theorem isPreprimitive_of_large_image [Fintype β] [htβ : IsPretransitive N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hM : IsPreprimitive M α)
    (hf' : Fintype.card β < 2 * Set.card (Set.range f)) : IsPreprimitive N β :=  by
  classical
  apply IsPreprimitive.mk
  intro B hB
  cases' subsingleton_or_nontrivial B with hB hB_nt
  · left; rwa [Set.subsingleton_coe] at hB
  dsimp only [IsTrivialBlock]
  rw [or_iff_not_imp_right]
  intro hB_ne_top
  -- Two ways of saying that B is nonempty
  have hB_ne : Set.Nonempty B := by
    rw [← Set.nonempty_coe_sort]
    apply Nontrivial.to_nonempty
  -- We reduce to proving `Fintype.card B < 2`
  rw [← Set.subsingleton_coe, ← Fintype.card_le_one_iff_subsingleton, ← Nat.lt_succ_iff]
  -- We reduce to proving that
  -- Fintype.card (Set.range f) ≤ Fintype.card (Set.range (λ g, g • B))
  apply lt_of_mul_lt_mul_right (lt_of_le_of_lt _ hf') (Nat.zero_le _)
  simp only [← Nat.card_eq_fintype_card, ← ncard_block_mul_ncard_orbit_eq hB hB_ne]
  apply Nat.mul_le_mul_left _
  -- We reduce to proving that
  -- fintype.card (set.range f ∩ g • B)) ≤ 1 for every g
  simp only [Nat.card_eq_fintype_card]
  simp only [← Set.toFinset_card]
  rw [Setoid.IsPartition.card_set_eq_sum_parts (Set.range f)
      (IsBlockSystem.of_block hB hB_ne).left]
  rw [Finset.card_eq_sum_ones]
  refine' Finset.sum_le_sum _
  intro t ht
  rw [Set.toFinset_card, Fintype.card_le_one_iff_subsingleton, Set.inter_comm,
    ← Set.image_preimage_eq_inter_range, Set.subsingleton_coe]

  -- It suffices to prove that the preimage is subsingleton
  simp only [Set.mem_toFinset, Set.mem_range] at ht
  obtain ⟨g, rfl⟩ := ht
  apply Set.Subsingleton.image
  -- Since the action of M on α is primitive, it suffices to prove that
  -- the preimage is a block which is not ⊤
  apply Or.resolve_right (hM.has_trivial_blocks (IsBlock_preimage f (IsBlock_of_block g hB)))
  intro h
  have h' : ⊤ ⊆ f ⁻¹' (g • B) := subset_of_eq h.symm
  rw [Set.top_eq_univ, ← Set.image_subset_iff, Set.image_univ] at h'
  -- We will prove that B is large, which will contradict the assumption that it is not ⊤
  apply hB_ne_top
  apply is_top_of_large_block hB
  -- It remains to show that fintype.card β < 2 * fintype.card B
  rw [Nat.card_eq_fintype_card]
  apply lt_of_lt_of_le hf'
  simp only [mul_le_mul_left, Nat.succ_pos']
  rw [← smul_set_card_eq g B]
  -- This last step is disgusting :
  -- the types are identical, but not the proofs that they are finite
  refine' le_trans _ (le_trans (Set.card_le_of_subset h') _)
  all_goals {
    simp only [Nat.card_eq_fintype_card]
    rfl }
#align is_preprimitive_of_large_image isPreprimitive_of_large_image

 -/

/-- The target of an equivariant map of large image is preprimitive if the source is -/
theorem isPreprimitive_of_large_image
    [Fintype β] [htβ : IsPretransitive N β] {φ : M → N}
    {f : α →ₑ[φ] β} (hM : IsPreprimitive M α)
    (hf' : Fintype.card β < 2 * Set.ncard (Set.range f)) :
    IsPreprimitive N β :=  by
  -- classical
  apply IsPreprimitive.mk
  intro B hB
  dsimp only [IsTrivialBlock]
  rcases Set.subsingleton_or_nontrivial B with (hB | hB)
  · left; exact hB
  right
  have := Setoid.IsPartition.card_set_eq_sum_parts (Set.range f)
      (IsBlockSystem.of_block hB hB_ne).left
  /-
  cases' Set.eq_empty_or_nonempty B with hBe hB_ne
  · rw [hBe]
    simp only [Set.ncard_empty, Nat.succ_pos']
  -- cases' Set.subsingleton_or_nontrivial B with hB hB_nt
  -- · left
  --   exact hB
  -- dsimp only [IsTrivialBlock]
  -- rw [or_iff_not_imp_right]
  -- intro hB_ne_top
  -- Two ways of saying that B is nonempty
--   have hB_ne : Set.Nonempty B := by
--    rw [← Set.nonempty_coe_sort]
--    apply Nontrivial.to_nonempty
  -- suffices : B.ncard < 2
  -- · rw [Nat.lt_succ_iff, Set.ncard_le_one_iff] at this
  --   intro x hx y hy
  --   exact this hx hy
-/

  -- We reduce to proving that
  -- Fintype.card (Set.range f) ≤ Fintype.card (Set.range (λ g, g • B))
  have := lt_of_mul_lt_mul_right (lt_of_le_of_lt _ hf') (Nat.zero_le _)
  simp only [← Nat.card_eq_fintype_card, ← ncard_block_mul_ncard_orbit_eq hB hB_ne]
  apply Nat.mul_le_mul_left _
  -- We reduce to proving that
  -- ncard (Set.range f ∩ g • B)) ≤ 1 for every g
  -- simp only [Nat.card_eq_fintype_card]
  classical
  simp only [Set.ncard_eq_toFinset_card']
  rw [Setoid.IsPartition.card_set_eq_sum_parts (Set.range f)
      (IsBlockSystem.of_block hB hB_ne).left]
  rw [Finset.card_eq_sum_ones]
  refine' Finset.sum_le_sum _
  intro t ht
  rw [← Set.ncard_eq_toFinset_card', ← Set.subsingleton_iff_ncard_le_one,
    Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  apply Set.Subsingleton.image
  -- It suffices to prove that the preimage is subsingleton
  simp only [Set.mem_toFinset, Set.mem_range] at ht
  obtain ⟨g, rfl⟩ := ht
  -- Since the action of M on α is primitive, it suffices to prove that
  -- the preimage is a block which is not ⊤
  apply Or.resolve_right
    (hM.has_trivial_blocks (IsBlock_preimage f (IsBlock_of_block g hB)))
  intro h
  apply hB_ne_top
  -- We will prove that B is large, which will contradict the assumption
  -- that it is not ⊤
  apply is_top_of_large_block hB
  -- It remains to show that fintype.card β < 2 * fintype.card B
  rw [Nat.card_eq_fintype_card]
  apply lt_of_lt_of_le hf'
  simp only [mul_le_mul_left, Nat.succ_pos', ← smul_set_ncard_eq g B]
  apply Set.ncard_le_ncard
  rw [← Set.image_univ, Set.image_subset_iff, ← Set.top_eq_univ, h]
  exact Set.toFinite (g • B)

/-- Theorem of Rudio (Wielandt, 1964, Th. 8.1) -/
theorem Rudio (hpGX : IsPreprimitive M α) (A : Set α) (hfA : A.Finite) (hA : A.Nonempty)
    (hA' : A ≠ ⊤) (a b : α) (h : a ≠ b) : ∃ g : M, a ∈ g • A ∧ b ∉ g • A :=
  by
  let B := ⋂ (g : M) (_ : a ∈ g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  -- B is a block hence is a trivial block
  cases' hpGX.has_trivial_blocks (IsBlock.of_subset a A hfA) with hyp hyp
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
#align rudio Rudio

end Finite

#lint
