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
import Mathlib.Data.Setoid.Partition

/-
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

open Pointwise

open MulAction

section IsTrivialBlock

variable {M α N β : Type*}

section monoid

variable [Monoid M] [MulAction M α] [Monoid N] [MulAction N β]

theorem IsTrivialBlock.image {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) {B : Set α} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f '' B) := by
  cases' hB with hB hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.top_eq_univ, Set.image_univ, Set.range_iff_surjective]
    exact hf

theorem IsTrivialBlock.preimage {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Injective f) {B : Set β} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f ⁻¹' B) := by
  cases' hB with hB hB
  apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  apply Or.intro_right; simp only [hB, Set.top_eq_univ]; apply Set.preimage_univ

end monoid

variable [Group M] [MulAction M α] [Monoid N] [MulAction N β]

theorem IsTrivialBlock.smul {B : Set α} (hB : IsTrivialBlock B) (g : M) :
    IsTrivialBlock (g • B) := by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MulAction.injective g)).mpr h
  | inr h =>
    right
    rw [h, Set.top_eq_univ, ← Set.image_smul]
    apply Set.image_univ_of_surjective
    exact MulAction.surjective g

theorem IsTrivialBlock.smul_iff {B : Set α} (g : M) :
    IsTrivialBlock (g • B) ↔ IsTrivialBlock B := by
  constructor
  · intro H
    convert IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

end IsTrivialBlock

section Primitive

variable (G : Type*) (X : Type*)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
class IsPreprimitive [SMul G X] extends IsPretransitive G X : Prop where
/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
  has_trivial_blocks' : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B

/-- A `mul_action` of a group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
class IsQuasipreprimitive [Group G] [MulAction G X] extends IsPretransitive G X : Prop where
/-- A `mul_action` of a group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
  pretransitive_of_normal :
    ∀ {N : Subgroup G} (_ : N.Normal), fixedPoints N X ≠ ⊤ → MulAction.IsPretransitive N X

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
    refine' H (g • B) _ (hB.smul g)
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
    exact H (g • B) ⟨b, hb, hg⟩ (IsBlock.smul g hB)

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

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M → N} {f : α →ₑ[φ] β}

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

theorem IsPreprimitive.iff_of_bijective
    (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β := by
  constructor
  apply IsPreprimitive.of_surjective hf.surjective
  intro hN
  haveI := (IsPretransitive.iff_of_bijective_map hφ hf).mpr hN.toIsPretransitive
  apply IsPreprimitive.mk
  · intro B hB
    rw [← Set.preimage_image_eq B hf.injective]
    apply IsTrivialBlock.preimage hf.injective
    exact hN.has_trivial_blocks (hB.image f hφ hf.injective)

end EquivariantMap

section Stabilizer

variable (G : Type*) [Group G] {X : Type*} [MulAction G X]

open scoped BigOperators Pointwise

instance Block.boundedOrderOfMem (a : X) :
    BoundedOrder { B : Set X // a ∈ B ∧ IsBlock G B } where
  top := ⟨⊤, by rw [Set.top_eq_univ]; apply Set.mem_univ, top_IsBlock X⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Set.top_eq_univ, Subtype.mk_le_mk, Set.le_eq_subset, Set.subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, isBlock_singleton a⟩
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
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a), OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
theorem hasMaximalStabilizersOfPreprimitive
    [hnX : Nontrivial X] (hpGX : IsPreprimitive G X) (a : X) :
    (stabilizer G a).IsMaximal := by
  haveI : IsPretransitive G X := hpGX.toIsPretransitive
  rw [maximal_stabilizer_iff_preprimitive]
  exact hpGX

end Stabilizer

section Normal

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]

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
  apply Or.resolve_left (hGX.has_trivial_blocks (orbit.isBlock_of_normal hN a))
  intro h
  apply ha; simp only [mem_fixedPoints]; intro n
  rw [← Set.mem_singleton_iff]
  suffices orbit N a = {a} by rw [← this]; use n
  · ext b
    rw [Set.Subsingleton.eq_singleton_of_mem h (MulAction.mem_orbit_self a)]

end Normal
