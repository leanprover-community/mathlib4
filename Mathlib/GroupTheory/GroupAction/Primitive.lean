/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Setoid.Partition.Card
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

## Particular results for actions on finite types

- `MulAction.IsPreprimitive.of_prime_card` :
  A pretransitive action on a finite type of prime cardinal is preprimitive.

- `MulAction.IsPreprimitive.of_card_lt`
  Given an equivariant map from a preprimitive action,
  if the image is at least twice the codomain, then the codomain is preprimitive.

- `MulAction.IsPreprimitive.exists_mem_smul_and_notMem_smul` : **Theorem of Rudio**.
  For a preprimitive action, a subset which is neither empty nor full has a translate
  which contains a given point and avoids another one.

-/

open Pointwise

namespace MulAction

variable (G : Type*) (X : Type*)

-- Note : if the action is degenerate, singletons may not be blocks.
/-- An additive action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
class _root_.AddAction.IsPreprimitive [VAdd G X] : Prop extends AddAction.IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, AddAction.IsBlock G B → AddAction.IsTrivialBlock B

/-- An action is preprimitive if it is pretransitive and
the only blocks are the trivial ones -/
@[to_additive]
class IsPreprimitive [SMul G X] : Prop extends IsPretransitive G X where
  /-- An action is preprimitive if it is pretransitive and
  the only blocks are the trivial ones -/
  isTrivialBlock_of_isBlock : ∀ {B : Set X}, IsBlock G B → IsTrivialBlock B

open IsPreprimitive

/-- An additive action of an additive group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
class _root_.AddAction.IsQuasiPreprimitive
    [AddGroup G] [AddAction G X] : Prop extends AddAction.IsPretransitive G X where
  isPretransitive_of_normal :
    ∀ {N : AddSubgroup G} [N.Normal], AddAction.fixedPoints N X ≠ .univ →
      AddAction.IsPretransitive N X

/-- An action of a group is quasipreprimitive if any normal subgroup
that has no fixed point acts pretransitively -/
@[to_additive]
class IsQuasiPreprimitive [Group G] [MulAction G X] : Prop extends IsPretransitive G X where
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

theorem isTrivialBlock_of_card_le_two
    [Finite X] (hX : Nat.card X ≤ 2) (B : Set X) :
    IsTrivialBlock B := by
  rw [IsTrivialBlock, ← B.ncard_le_one_iff_subsingleton, B.eq_univ_iff_ncard]
  have := B.ncard_le_card
  grind

variable [Group G] [MulAction G X]

open scoped BigOperators Pointwise

/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/
@[to_additive
/-- If the action is pretransitive, then the trivial blocks condition implies preprimitivity
(based condition) -/]
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
  /-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
  (pretransitivity is automatic) (based condition) -/]
theorem IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints {a : X} (ha : a ∉ fixedPoints G X)
    (H : ∀ ⦃B : Set X⦄, a ∈ B → IsBlock G B → IsTrivialBlock B) :
    IsPreprimitive G X :=
  have : IsPretransitive G X := by
    rw [isPretransitive_iff_base a]
    rcases H (mem_orbit_self a) (IsBlock.orbit a) with H | H
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

@[deprecated (since := "2025-05-23")]
alias _root_.AddAction.IsPreprimitive.of_isTrivialBlock_of_not_mem_fixedPoints :=
  AddAction.IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints

@[to_additive existing, deprecated (since := "2025-05-23")]
alias IsPreprimitive.of_isTrivialBlock_of_not_mem_fixedPoints :=
  IsPreprimitive.of_isTrivialBlock_of_notMem_fixedPoints

/-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/
@[to_additive
  /-- If the action is not trivial, then the trivial blocks condition implies preprimitivity
(pretransitivity is automatic) -/]
theorem IsPreprimitive.mk' (Hnt : fixedPoints G X ≠ ⊤)
    (H : ∀ {B : Set X} (_ : IsBlock G B), IsTrivialBlock B) :
    IsPreprimitive G X := by
  simp only [Set.top_eq_univ, Set.ne_univ_iff_exists_notMem] at Hnt
  obtain ⟨_, ha⟩ := Hnt
  exact .of_isTrivialBlock_of_notMem_fixedPoints ha fun {B} _ ↦ H

@[deprecated (since := "2025-03-03")] alias _root_.AddAction.mk' := AddAction.IsPreprimitive.mk'
@[to_additive existing, deprecated (since := "2025-03-03")] alias mk' := IsPreprimitive.mk'

section EquivariantMap

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]
variable {N β : Type*} [Group N] [MulAction N β]
variable {φ : M → N} {f : α →ₑ[φ] β}

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
  /-- A pretransitive action on a nontrivial type is preprimitive iff
  the set of blocks containing a given element is a simple order -/]
theorem isSimpleOrder_blockMem_iff_isPreprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsSimpleOrder (BlockMem G a) ↔ IsPreprimitive G X := by
  constructor
  · intro h; let h_bot_or_top := h.eq_bot_or_eq_top
    apply IsPreprimitive.of_isTrivialBlock_base a
    intro B haB hB
    rcases h_bot_or_top ⟨B, haB, hB⟩ with hB' | hB' <;>
      simp only [← Subtype.coe_inj] at hB'
    · left; rw [hB']; exact Set.subsingleton_singleton
    · right; rw [hB']; rfl
  · intro hGX'; apply IsSimpleOrder.mk
    rintro ⟨B, haB, hB⟩
    simp only [← Subtype.coe_inj]
    cases hGX'.isTrivialBlock_of_isBlock hB with
    | inl h =>
      simp [BlockMem.coe_bot, h.eq_singleton_of_mem haB]
    | inr h =>
      simp [BlockMem.coe_top, h]

/-- A pretransitive action is preprimitive
iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/
@[to_additive
  /-- A pretransitive action is preprimitive
  iff the stabilizer of any point is a maximal subgroup (Wielandt, th. 7.5) -/]
theorem isCoatom_stabilizer_iff_preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsCoatom (stabilizer G a) ↔ IsPreprimitive G X := by
  rw [← isSimpleOrder_blockMem_iff_isPreprimitive G a, ← Set.isSimpleOrder_Ici_iff_isCoatom]
  simp only [isSimpleOrder_iff_isCoatom_bot]
  rw [← OrderIso.isCoatom_iff (block_stabilizerOrderIso G a), OrderIso.map_bot]

/-- In a preprimitive action, stabilizers are maximal subgroups -/
@[to_additive /-- In a preprimitive action, stabilizers are maximal subgroups. -/]
theorem IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    [Nontrivial X] [IsPreprimitive G X] (a : X) :
    IsCoatom (stabilizer G a) := by
  rwa [isCoatom_stabilizer_iff_preprimitive]

end Stabilizer

section Normal

variable {M : Type*} [Group M] {α : Type*} [MulAction M α]

/-- In a preprimitive action, any normal subgroup that acts nontrivially is pretransitive
(Wielandt, th. 7.1). -/
@[to_additive /-- In a preprimitive additive action,
  any normal subgroup that acts nontrivially is pretransitive (Wielandt, th. 7.1). -/]
-- See note [lower instance priority]
instance (priority := 100) IsPreprimitive.isQuasiPreprimitive [IsPreprimitive M α] :
    IsQuasiPreprimitive M α where
  isPretransitive_of_normal {N} _ hNX := by
    rw [Set.ne_univ_iff_exists_notMem] at hNX
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

section Finite

namespace IsPreprimitive

variable {H Y : Type*} [Group H] [MulAction H Y]

/-- A pretransitive action on a set of prime order is preprimitive -/
@[to_additive /-- A pretransitive action on a set of prime order is preprimitive -/]
theorem of_prime_card [hGX : IsPretransitive G X] (hp : Nat.Prime (Nat.card X)) :
    IsPreprimitive G X := by
  refine ⟨fun {B} hB ↦ B.subsingleton_or_nontrivial.imp id fun hB' ↦ ?_⟩
  have : Finite X := (Nat.card_ne_zero.mp hp.ne_zero).2
  rw [Set.eq_univ_iff_ncard, eq_comm, ← hp.dvd_iff_eq ((Set.one_lt_ncard).mpr hB').ne']
  exact hB.ncard_dvd_card hB'.nonempty

variable {φ : G → H} {f : X →ₑ[φ] Y}

/-- The codomain of an equivariant map of large image is preprimitive if the domain is. -/
@[to_additive
/-- The codomain of an equivariant map of large image is preprimitive if the domain is. -/]
theorem of_card_lt [Finite Y] [IsPretransitive H Y] [IsPreprimitive G X]
    (hf' : Nat.card Y < 2 * (Set.range f).ncard) :
    IsPreprimitive H Y := by
  refine ⟨fun {B} hB ↦ ?_⟩
  rcases B.eq_empty_or_nonempty with hB' | hB'; · simp [IsTrivialBlock, hB']
  rw [IsTrivialBlock, or_iff_not_imp_right]
  intro hB_ne_top
  -- we need Set.Subsingleton B ↔ Set.ncard B ≤ 1
  suffices Set.ncard B < 2 by simpa [Nat.lt_succ_iff] using this
  -- We reduce to proving that (Set.range f).ncard ≤ (orbit N B).ncard
  apply lt_of_mul_lt_mul_right (lt_of_le_of_lt _ hf') (zero_le _)
  simp only [← hB.ncard_block_mul_ncard_orbit_eq hB']
  apply Nat.mul_le_mul_left
  -- We reduce to proving that (Set.range f ∩ g • B).ncard ≤ 1 for every g
  have hfin := Fintype.ofFinite (Set.range fun g : H ↦ g • B)
  rw [(hB.isBlockSystem hB').left.ncard_eq_finsum, finsum_eq_sum_of_fintype]
  apply le_trans (Finset.sum_le_card_nsmul _ _ 1 _)
  · rw [nsmul_one, Finset.card_univ, ← Set.toFinset_card, ← Set.ncard_eq_toFinset_card',
      orbit, Nat.cast_id]
  · rintro ⟨x, ⟨g, rfl⟩⟩ -
    suffices Set.Subsingleton (Set.range f ∩ g • B) by simpa
    -- It suffices to prove that the preimage is subsingleton
    rw [← Set.image_preimage_eq_range_inter]
    apply Set.Subsingleton.image
    -- Since the action of M on α is primitive, it suffices to prove that
    -- the preimage is a block which is not ⊤
    apply Or.resolve_right (isTrivialBlock_of_isBlock ((hB.translate g).preimage f))
    intro h
    simp only [Set.preimage_eq_univ_iff] at h
    -- We will prove that B is large, which will contradict the assumption that it is not ⊤
    apply hB_ne_top
    apply hB.eq_univ_of_card_lt
    -- It remains to show that Nat.card β < Set.ncard B * 2
    apply lt_of_lt_of_le hf'
    rw [mul_comm, mul_le_mul_iff_left₀ Nat.succ_pos']
    apply le_trans (Set.ncard_le_ncard h) (Set.ncard_image_le B.toFinite)

/- The finiteness assumption is necessary :
  For G = ℤ acting on itself, no translate of ℕ contains 0 but not 1.
  (See comment before `IsBlock.of_subset`.) -/
/-- Theorem of Rudio (Wielandt, 1964, Th. 8.1)

For a preprimitive action, a subset which is neither empty nor full has a translate
which contains a given point and avoids another one. -/
@[to_additive /-- Theorem of Rudio (Wielandt, 1964, Th. 8.1)

For a preprimitive additive action, a subset which is neither empty nor full has a translate
which contains a given point and avoids another one. -/]
theorem exists_mem_smul_and_notMem_smul [IsPreprimitive G X]
    {A : Set X} (hfA : A.Finite) (hA : A.Nonempty) (hA' : A ≠ .univ) {a b : X} (h : a ≠ b) :
    ∃ g : G, a ∈ g • A ∧ b ∉ g • A := by
  let B := ⋂ (g : G) (_ : a ∈ g • A), g • A
  suffices b ∉ B by
    rw [Set.mem_iInter] at this
    simpa only [Set.mem_iInter, not_forall, exists_prop] using this
  suffices B = {a} by rw [this]; rw [Set.mem_singleton_iff]; exact Ne.symm h
  -- B is a block hence is a trivial block
  rcases isTrivialBlock_of_isBlock (G := G) (IsBlock.of_subset a hfA) with hyp | hyp
  · -- B.subsingleton
    apply Set.Subsingleton.eq_singleton_of_mem hyp
    rw [Set.mem_iInter]; intro g; simp only [Set.mem_iInter, imp_self]
  · -- B = Set.univ: contradiction
    change B = Set.univ at hyp
    exfalso; apply hA'
    suffices ∃ g : G, a ∈ g • A by
      obtain ⟨g, hg⟩ := this
      have : B ⊆ g • A := Set.biInter_subset_of_mem hg
      rw [hyp, Set.univ_subset_iff, ← eq_inv_smul_iff] at this
      rw [this, Set.smul_set_univ]
    -- ∃ (g : M), a ∈ g • A
    obtain ⟨x, hx⟩ := hA
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x a
    use g, x

@[deprecated (since := "2025-05-23")]
alias _root_.AddAction.IsPreprimitive.exists_mem_vadd_and_not_mem_vadd :=
  AddAction.IsPreprimitive.exists_mem_vadd_and_notMem_vadd

@[to_additive existing, deprecated (since := "2025-05-23")]
alias exists_mem_smul_and_not_mem_smul := exists_mem_smul_and_notMem_smul

end IsPreprimitive

end Finite

end MulAction
