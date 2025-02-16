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

- `MulAction.IsPreprimitive G X`
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
  which further assumes that `X` is not empty.

- `MulAction.IsQuasiPreprimitive G X`
  A structure that says that the action of the group `G` on the type `X` is *quasipreprimitive*,
  namely, normal subgroups of `G` which act nontrivially act pretransitively.

- We prove some straightforward theorems that relate preprimitivity
  under equivariant maps, for images and preimages.

## Relation with stabilizers

- `MulAction.isSimpleOrderBlockMem_iff_isPreprimitive`
  relates primitivity and the fact that the inclusion order on blocks containing is simple.

- `MulAction.isCoatom_stabilizer_iff_preprimitive`
  An action is preprimitive iff the stabilizers of points are maximal subgroups.

- `MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive`
  Stabilizers of points under a preprimitive action are maximal subgroups.

## Relation with normal subgroups

- `MulAction.IsPreprimitive.isQuasipreprimitive`
  Preprimitive actions are quasipreprimitive.

-/

open Pointwise

namespace MulAction

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
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B

open IsPreprimitive

/-- An additive action of an additive group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
class _root_.AddAction.IsQuasiPreprimitive
    [AddGroup G] [AddAction G X] extends AddAction.IsPretransitive G X : Prop where
  isPretransitive_of_normal :
    ∀ {N : AddSubgroup G} [N.Normal], AddAction.fixedPoints N X ≠ .univ →
      AddAction.IsPretransitive N X

/-- An action of a group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
@[to_additive]
class IsQuasiPreprimitive [Group G] [MulAction G X] extends IsPretransitive G X : Prop where
  isPretransitive_of_normal :
    ∀ {N : Subgroup G} [N.Normal], fixedPoints N X ≠ .univ → IsPretransitive N X

variable {G X}

@[to_additive]
theorem IsBlock.subsingleton_or_eq_univ
    [SMul G X] [IsPreprimitive G X] {B : Set X} (hB : IsBlock G B) :
    B.Subsingleton ∨ B = .univ :=
  isTrivialBlock_of_isBlock hB

@[to_additive (attr := nontriviality)]
theorem IsPreprimitive.of_subsingleton [SMul G X] [Nonempty G] [Subsingleton X] :
    IsPreprimitive G X where
  exists_smul_eq (x y) := by
    use Classical.arbitrary G
    rw [eq_iff_true_of_subsingleton]
    trivial
  isTrivialBlock_of_isBlock B := by
    left
    exact Set.subsingleton_of_subsingleton

variable [Group G] [MulAction G X]

open scoped BigOperators Pointwise

/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/
@[to_additive
"If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition)"]
theorem IsPreprimitive.of_isTrivialBlock_base [IsPretransitive G X] (a : X)
    (H : ∀ {B : Set X} (_ : a ∈ B) (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X where
  isTrivialBlock_of_isBlock {B} hB := by
    obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
    · simp [IsTrivialBlock]
    · obtain ⟨g, hg⟩ := exists_smul_eq G b a
      rw [← IsTrivialBlock.smul_iff g]
      apply H _ (hB.translate g)
      rw [← hg]
      use b

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) (based condition) -/
@[to_additive
  "If the action is not trivial, then the trivial blocks condition implies preprimitivity
  (pretransitivity is automatic) (based condition)"]
theorem IsPreprimitive.of_isTrivialBlock_of_not_mem_fixedPoints {a : X} (ha : a ∉ fixedPoints G X)
    (H : ∀ ⦃B : Set X⦄, a ∈ B → IsBlock G B → IsTrivialBlock B) :
    IsPreprimitive G X :=
  have : IsPretransitive G X := by
    rw [isPretransitive_iff_base a]
    cases' H (mem_orbit_self a) (IsBlock.orbit a) with H H
    · exfalso; apply ha
      rw [Set.subsingleton_iff_singleton (mem_orbit_self a)] at H
      simp only [mem_fixedPoints]
      intro g
      rw [← Set.mem_singleton_iff]; rw [← H]
      exact mem_orbit a g
    · intro x; rw [← MulAction.mem_orbit_iff, H]; exact Set.mem_univ x
  { isTrivialBlock_of_isBlock {B} hB := by
      obtain rfl | ⟨b, hb⟩ := B.eq_empty_or_nonempty
      · simp [IsTrivialBlock]
      · obtain ⟨g, hg⟩ := exists_smul_eq G b a
        rw [← IsTrivialBlock.smul_iff g]
        exact H ⟨b, hb, hg⟩ (hB.translate g) }

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/
@[to_additive
  "If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic)"]
theorem mk' (Hnt : fixedPoints G X ≠ ⊤)
    (H : ∀ {B : Set X} (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_not_mem] at Hnt
  obtain ⟨_, ha⟩ := Hnt
  exact .of_isTrivialBlock_of_not_mem_fixedPoints ha fun {B} _ ↦ H

section EquivariantMap

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M →* N} {f : α →ₑ[φ] β}

@[to_additive]
theorem IsPreprimitive.of_surjective [IsPreprimitive M α] (hf : Function.Surjective f) :
    IsPreprimitive N β where
  toIsPretransitive := toIsPretransitive.of_surjective_map hf
  isTrivialBlock_of_isBlock {B} hB := by
    rw [← Set.image_preimage_eq B hf]
    apply IsTrivialBlock.image hf
    exact isTrivialBlock_of_isBlock (IsBlock.preimage f hB)

@[to_additive]
theorem isPreprimitive_congr (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β := by
  constructor
  · intro _
    apply IsPreprimitive.of_surjective hf.surjective
  · intro _
    haveI := (isPretransitive_congr hφ hf).mpr toIsPretransitive
    exact {
      isTrivialBlock_of_isBlock {B} hB := by
        rw [← Set.preimage_image_eq B hf.injective]
        exact IsTrivialBlock.preimage hf.injective
          (isTrivialBlock_of_isBlock (hB.image f hφ hf.injective)) }

end EquivariantMap

section Stabilizer

variable (G : Type*) [Group G] {X : Type*} [MulAction G X]

open scoped BigOperators Pointwise

/-- A pretransitive action on a nontrivial type is preprimitive iff
the set of blocks containing a given element is a simple order -/
@[to_additive (attr := simp)
  "A pretransitive action on a nontrivial type is preprimitive iff
  the set of blocks containing a given element is a simple order"]
theorem isSimpleOrder_blockMem_iff_isPreprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsSimpleOrder (BlockMem G a) ↔ IsPreprimitive G X := by
  constructor
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.of_isTrivialBlock_base a
    intro B haB hB
    rcases h_bot_or_top ⟨B, haB, hB⟩ with hB' | hB' <;>
      simp only [← Subtype.coe_inj, Subtype.coe_mk] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · right; rw [hB']; rfl
  · intro hGX'; apply IsSimpleOrder.mk
    rintro ⟨B, haB, hB⟩
    simp only [← Subtype.coe_inj, Subtype.coe_mk]
    cases hGX'.isTrivialBlock_of_isBlock hB with
    | inl h =>
      simp [BlockMem.coe_bot, h.eq_singleton_of_mem haB]
    | inr h =>
      simp [BlockMem.coe_top, h]

/-- A pretransitive action is preprimitive
iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
@[to_additive
  "A pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5)"]
theorem isCoatom_stabilizer_iff_preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsCoatom (stabilizer G a) ↔ IsPreprimitive G X := by
  rw [← isSimpleOrder_blockMem_iff_isPreprimitive G a, ← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a), OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
@[to_additive "In a preprimitive action, stabilizers are maximal subgroups."]
theorem IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    [Nontrivial X] [IsPreprimitive G X] (a : X) :
    IsCoatom (stabilizer G a) := by
  rwa [isCoatom_stabilizer_iff_preprimitive]

end Stabilizer

section Normal

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]

/-- In a preprimitive action, any normal subgroup that acts nontrivially is pretransitive
(Wielandt, th. 7.1)-/
@[to_additive "In a preprimitive additive action,
  any normal subgroup that acts nontrivially is pretransitive (Wielandt, th. 7.1)"]
-- See note [lower instance priority]
instance (priority := 100) IsPreprimitive.isQuasiPreprimitive [IsPreprimitive M α] :
    IsQuasiPreprimitive M α where
  isPretransitive_of_normal {N} _ hNX := by
    rw [Set.ne_univ_iff_exists_not_mem] at hNX
    obtain ⟨a, ha⟩ := hNX
    rw [isPretransitive_iff_orbit_eq_univ a]
    apply Or.resolve_left (isTrivialBlock_of_isBlock (IsBlock.orbit_of_normal a))
    intro h
    apply ha
    simp only [mem_fixedPoints]
    intro n
    rw [← Set.mem_singleton_iff]
    suffices orbit N a = {a} by rw [← this]; use n
    ext b
    rw [Set.Subsingleton.eq_singleton_of_mem h (MulAction.mem_orbit_self a)]

end Normal

end MulAction
