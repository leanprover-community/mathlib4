/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

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
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, AddAction.IsBlock G B → AddAction.IsTrivialBlock B

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

/-- A `MulAction` of a group is quasipreprimitive if any normal subgroup
  that has no fixed point acts pretransitively -/
@[to_additive]
class IsQuasipreprimitive [Group G] [MulAction G X] extends IsPretransitive G X : Prop where
  pretransitive_of_normal :
    ∀ {N : Subgroup G} (_ : N.Normal), fixedPoints N X ≠ ⊤ → IsPretransitive N X

variable {G X}

namespace IsPreprimitive

@[to_additive]
theorem subsingleton_or_eq_univ_of_isBlock [SMul G X] (h : IsPreprimitive G X) {B : Set X}
    (hB : IsBlock G B) : B.Subsingleton ∨ B = univ := by apply h.has_trivial_blocks'; exact hB

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
    | inl h =>
      simp [BlockMem.coe_bot, h.eq_singleton_of_mem haB]
    | inr h =>
      simp [BlockMem.coe_top, h]
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.mk_mem_of_pretransitive a
    intro B haB hB
    cases' h_bot_or_top ⟨B, haB, hB⟩ with hB' hB' <;>
      simp only [← Subtype.coe_inj, Subtype.coe_mk] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · right; rw [hB']; rfl

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
    [hnX : Nontrivial X] (hpGX : IsPreprimitive G X) (a : X) :
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

end Primitive

end MulAction
