/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Setoid.Partition
import Mathlib.GroupTheory.GroupAction.Pointwise
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.IntervalCases

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `MulAction.IsBlock G B` states that `B : Set X` is a block,
  which means that the sets `g • B`, for `g ∈ G`, are equal or disjoint.
  Under `Group G` and `MulAction G X`, this is equivalent to the classical
  definition `MulAction.IsBlock.def_one`

- a bunch of lemmas that give examples of “trivial” blocks : ⊥, ⊤, singletons,
  and non-trivial blocks: orbit of the group, orbit of a normal subgroup…

The non-existence of nontrivial blocks is the definition of primitive actions.

## Results for actions on finite sets

- `MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq` : The cardinality of a block
  multiplied by the number of its translates is the cardinal of the ambient type

- `MulAction.IsBlock.eq_univ_of_card_lt` : a too large block is equal to `Set.univ`

- `MulAction.IsBlock.subsingleton_of_card_lt` : a too small block is a subsingleton

- `MulAction.IsBlock.of_subset` : the intersections of the translates of a finite subset
  that contain a given point is a block

- `MulAction.BlockMem` : the type of blocks containing a given element

- `MulAction.BlockMem.instBoundedOrder` :
  the type of blocks containing a given element is a bounded order.

## References

We follow [Wielandt-1964].

-/

open Set
open scoped Pointwise

namespace MulAction

section orbits

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

@[to_additive]
theorem orbit.eq_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) := by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp +contextual
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, eq_comm, implies_true]

@[to_additive]
theorem orbit.pairwiseDisjoint :
    (Set.range fun x : X => orbit G x).PairwiseDisjoint id := by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

/-- Orbits of an element form a partition -/
@[to_additive /-- Orbits of an element form a partition -/]
theorem IsPartition.of_orbits :
    Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MulAction.nonempty_orbit a).ne_empty ha

end orbits

section SMul

variable (G : Type*) {X : Type*} [SMul G X] {B : Set X} {a : X}

-- Change terminology to IsFullyInvariant?
/-- A set `B` is a `G`-fixed block if `g • B = B` for all `g : G`. -/
@[to_additive /-- A set `B` is a `G`-fixed block if `g +ᵥ B = B` for all `g : G`. -/]
def IsFixedBlock (B : Set X) := ∀ g : G, g • B = B

/-- A set `B` is a `G`-invariant block if `g • B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A set `B` is a `G`-invariant block if `g +ᵥ B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/]
def IsInvariantBlock (B : Set X) := ∀ g : G, g • B ⊆ B

section IsTrivialBlock

/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/]
def IsTrivialBlock (B : Set X) := B.Subsingleton ∨ B = univ

variable {M α N β : Type*}

section monoid

variable [Monoid M] [MulAction M α] [Monoid N] [MulAction N β]

@[to_additive]
theorem IsTrivialBlock.image {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) {B : Set α} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f '' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.image_univ, Set.range_eq_univ, hf]

@[to_additive]
theorem IsTrivialBlock.preimage {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Injective f) {B : Set β} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f ⁻¹' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  · apply Or.intro_right; simp only [hB]; apply Set.preimage_univ

end monoid

variable [Group M] [MulAction M α] [Monoid N] [MulAction N β]

@[to_additive]
theorem IsTrivialBlock.smul {B : Set α} (hB : IsTrivialBlock B) (g : M) :
    IsTrivialBlock (g • B) := by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MulAction.injective g)).mpr h
  | inr h =>
    right
    rw [h, ← Set.image_smul, Set.image_univ_of_surjective (MulAction.surjective g)]

@[to_additive]
theorem IsTrivialBlock.smul_iff {B : Set α} (g : M) :
    IsTrivialBlock (g • B) ↔ IsTrivialBlock B := by
  constructor
  · intro H
    convert IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

end IsTrivialBlock

/-- A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint. -/
@[to_additive
/-- A set `B` is a `G`-block iff the sets of the form `g +ᵥ B` are pairwise equal or disjoint. -/]
def IsBlock (B : Set X) := ∀ ⦃g₁ g₂ : G⦄, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B)

variable {G} {s : Set G} {g g₁ g₂ : G}

@[to_additive]
lemma isBlock_iff_smul_eq_smul_of_nonempty :
    IsBlock G B ↔ ∀ ⦃g₁ g₂ : G⦄, (g₁ • B ∩ g₂ • B).Nonempty → g₁ • B = g₂ • B := by
  simp_rw [IsBlock, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]
lemma isBlock_iff_pairwiseDisjoint_range_smul :
    IsBlock G B ↔ (range fun g : G ↦ g • B).PairwiseDisjoint id := pairwiseDisjoint_range_iff.symm

@[to_additive]
lemma isBlock_iff_smul_eq_smul_or_disjoint :
    IsBlock G B ↔ ∀ g₁ g₂ : G, g₁ • B = g₂ • B ∨ Disjoint (g₁ • B) (g₂ • B) :=
  forall₂_congr fun _ _ ↦ or_iff_not_imp_left.symm

@[to_additive]
lemma IsBlock.smul_eq_smul_of_subset (hB : IsBlock G B) (hg : g₁ • B ⊆ g₂ • B) :
    g₁ • B = g₂ • B := by
  by_contra! hg'
  obtain rfl : B = ∅ := by simpa using (hB hg').eq_bot_of_le hg
  simp at hg'

@[to_additive]
lemma IsBlock.not_smul_set_ssubset_smul_set (hB : IsBlock G B) : ¬ g₁ • B ⊂ g₂ • B :=
  fun hab ↦ hab.ne <| hB.smul_eq_smul_of_subset hab.subset

@[to_additive]
lemma IsBlock.disjoint_smul_set_smul (hB : IsBlock G B) (hgs : ¬ g • B ⊆ s • B) :
    Disjoint (g • B) (s • B) := by
  rw [← iUnion_smul_set, disjoint_iUnion₂_right]
  exact fun b hb ↦ hB fun h ↦ hgs <| h.trans_subset <| smul_set_subset_smul hb

@[to_additive]
lemma IsBlock.disjoint_smul_smul_set (hB : IsBlock G B) (hgs : ¬ g • B ⊆ s • B) :
    Disjoint (s • B) (g • B) := (hB.disjoint_smul_set_smul hgs).symm

@[to_additive]
alias ⟨IsBlock.smul_eq_smul_of_nonempty, _⟩ := isBlock_iff_smul_eq_smul_of_nonempty
@[to_additive]
alias ⟨IsBlock.pairwiseDisjoint_range_smul, _⟩ := isBlock_iff_pairwiseDisjoint_range_smul
@[to_additive]
alias ⟨IsBlock.smul_eq_smul_or_disjoint, _⟩ := isBlock_iff_smul_eq_smul_or_disjoint

/-- A fixed block is a block. -/
@[to_additive /-- A fixed block is a block. -/]
lemma IsFixedBlock.isBlock (hfB : IsFixedBlock G B) : IsBlock G B := by simp [IsBlock, hfB _]

/-- The empty set is a block. -/
@[to_additive (attr := simp) /-- The empty set is a block. -/]
lemma IsBlock.empty : IsBlock G (∅ : Set X) := by simp [IsBlock]

/-- A singleton is a block. -/
@[to_additive /-- A singleton is a block. -/]
lemma IsBlock.singleton : IsBlock G ({a} : Set X) := by simp [IsBlock]

/-- Subsingletons are (trivial) blocks. -/
@[to_additive /-- Subsingletons are (trivial) blocks. -/]
lemma IsBlock.of_subsingleton (hB : B.Subsingleton) : IsBlock G B :=
  hB.induction_on .empty fun _ ↦ .singleton

/-- A fixed block is an invariant block. -/
@[to_additive /-- A fixed block is an invariant block. -/]
lemma IsFixedBlock.isInvariantBlock (hB : IsFixedBlock G B) : IsInvariantBlock G B :=
  fun _ ↦ (hB _).le

end SMul

section Monoid
variable {M X : Type*} [Monoid M] [MulAction M X] {B : Set X} {s : Set M}

@[to_additive]
lemma IsBlock.disjoint_smul_right (hB : IsBlock M B) (hs : ¬ B ⊆ s • B) : Disjoint B (s • B) := by
  simpa using hB.disjoint_smul_set_smul (g := 1) (by simpa using hs)

@[to_additive]
lemma IsBlock.disjoint_smul_left (hB : IsBlock M B) (hs : ¬ B ⊆ s • B) : Disjoint (s • B) B :=
  (hB.disjoint_smul_right hs).symm

end Monoid

section Group

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] {B : Set X}

@[to_additive]
lemma isBlock_iff_disjoint_smul_of_ne :
    IsBlock G B ↔ ∀ ⦃g : G⦄, g • B ≠ B → Disjoint (g • B) B := by
  refine ⟨fun hB g ↦ by simpa using hB (g₂ := 1), fun hB g₁ g₂ h ↦ ?_⟩
  simp only [disjoint_smul_set_right, ne_eq, ← inv_smul_eq_iff, smul_smul] at h ⊢
  exact hB h

@[to_additive]
lemma isBlock_iff_smul_eq_of_nonempty :
    IsBlock G B ↔ ∀ ⦃g : G⦄, (g • B ∩ B).Nonempty → g • B = B := by
  simp_rw [isBlock_iff_disjoint_smul_of_ne, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[to_additive]
lemma isBlock_iff_smul_eq_or_disjoint :
    IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B :=
  isBlock_iff_disjoint_smul_of_ne.trans <| forall_congr' fun _ ↦ or_iff_not_imp_left.symm

@[to_additive]
lemma isBlock_iff_smul_eq_of_mem :
    IsBlock G B ↔ ∀ ⦃g : G⦄ ⦃a : X⦄, a ∈ B → g • a ∈ B → g • B = B := by
  simp [isBlock_iff_smul_eq_of_nonempty, Set.Nonempty, mem_smul_set]

@[to_additive] alias ⟨IsBlock.disjoint_smul_of_ne, _⟩ := isBlock_iff_disjoint_smul_of_ne
@[to_additive] alias ⟨IsBlock.smul_eq_of_nonempty, _⟩ := isBlock_iff_smul_eq_of_nonempty
@[to_additive] alias ⟨IsBlock.smul_eq_or_disjoint, _⟩ := isBlock_iff_smul_eq_or_disjoint
@[to_additive] alias ⟨IsBlock.smul_eq_of_mem, _⟩ := isBlock_iff_smul_eq_of_mem

-- TODO: Generalise to `SubgroupClass`
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/
@[to_additive
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/]
lemma IsBlock.subgroup {H : Subgroup G} (hB : IsBlock G B) : IsBlock H B := fun _ _ h ↦ hB h

/-- A block of a group action is invariant iff it is fixed. -/
@[to_additive /-- A block of a group action is invariant iff it is fixed. -/]
lemma isInvariantBlock_iff_isFixedBlock : IsInvariantBlock G B ↔ IsFixedBlock G B :=
  ⟨fun hB g ↦ (hB g).antisymm <| subset_smul_set_iff.2 <| hB _, IsFixedBlock.isInvariantBlock⟩

/-- An invariant block of a group action is a fixed block. -/
@[to_additive /-- An invariant block of a group action is a fixed block. -/]
alias ⟨IsInvariantBlock.isFixedBlock, _⟩ := isInvariantBlock_iff_isFixedBlock

/-- An invariant block  of a group action is a block. -/
@[to_additive /-- An invariant block of a group action is a block. -/]
lemma IsInvariantBlock.isBlock (hB : IsInvariantBlock G B) : IsBlock G B := hB.isFixedBlock.isBlock

/-- The full set is a fixed block. -/
@[to_additive /-- The full set is a fixed block. -/]
lemma IsFixedBlock.univ : IsFixedBlock G (univ : Set X) := fun _ ↦ by simp

/-- The full set is a block. -/
@[to_additive (attr := simp) /-- The full set is a block. -/]
lemma IsBlock.univ : IsBlock G (univ : Set X) := IsFixedBlock.univ.isBlock

/-- The intersection of two blocks is a block. -/
@[to_additive /-- The intersection of two blocks is a block. -/]
lemma IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ ∩ B₂) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter] at h₁ h₂ ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  rw [h₁ ⟨a, ha₁.1, ha₂.1⟩, h₂ ⟨a, ha₁.2, ha₂.2⟩]

/-- An intersection of blocks is a block. -/
@[to_additive /-- An intersection of blocks is a block. -/]
lemma IsBlock.iInter {ι : Sort*} {B : ι → Set X} (hB : ∀ i, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_iInter] at hB ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  simp_rw [fun i ↦ hB i ⟨a, iInter_subset _ i ha₁, iInter_subset _ i ha₂⟩]

/-- A trivial block is a block. -/
@[to_additive /-- A trivial block is a block. -/]
lemma IsTrivialBlock.isBlock (hB : IsTrivialBlock B) : IsBlock G B := by
  obtain hB | rfl := hB
  · exact .of_subsingleton hB
  · exact .univ

/-- An orbit is a fixed block. -/
@[to_additive /-- An orbit is a fixed block. -/]
protected lemma IsFixedBlock.orbit (a : X) : IsFixedBlock G (orbit G a) := (smul_orbit · a)

/-- An orbit is a block. -/
@[to_additive /-- An orbit is a block. -/]
protected lemma IsBlock.orbit (a : X) : IsBlock G (orbit G a) := (IsFixedBlock.orbit a).isBlock

@[to_additive]
lemma isBlock_top : IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B :=
  Subgroup.topEquiv.toEquiv.forall_congr fun _ ↦ Subgroup.topEquiv.toEquiv.forall_congr_left

@[to_additive]
lemma IsBlock.preimage {H Y : Type*} [Group H] [MulAction H Y]
    {φ : H → G} (j : Y →ₑ[φ] X) (hB : IsBlock G B) :
    IsBlock H (j ⁻¹' B) := by
  rintro g₁ g₂ hg
  rw [← Group.preimage_smul_setₛₗ, ← Group.preimage_smul_setₛₗ] at hg ⊢
  exact (hB <| ne_of_apply_ne _ hg).preimage _

@[to_additive]
theorem IsBlock.image {H Y : Type*} [SMul H Y] {φ : G → H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j) (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
  exact fun g₁ g₂ hg ↦ disjoint_image_of_injective hj <| hB <| ne_of_apply_ne _ hg

@[to_additive]
theorem IsBlock.subtype_val_preimage {C : SubMulAction G X} (hB : IsBlock G B) :
    IsBlock G (Subtype.val ⁻¹' B : Set C) :=
  hB.preimage C.inclusion

@[to_additive]
theorem isBlock_subtypeVal {C : SubMulAction G X} {B : Set C} :
    IsBlock G (Subtype.val '' B : Set X) ↔ IsBlock G B := by
  refine forall₂_congr fun g₁ g₂ ↦ ?_
  rw [← SubMulAction.inclusion.coe_eq, ← image_smul_set, ← image_smul_set, ne_eq,
    Set.image_eq_image C.inclusion_injective, disjoint_image_iff C.inclusion_injective]

theorem _root_.AddAction.IsBlock.of_addSubgroup_of_conjugate
    {G : Type*} [AddGroup G] {X : Type*} [AddAction G X] {B : Set X}
    {H : AddSubgroup G} (hB : AddAction.IsBlock H B) (g : G) :
    AddAction.IsBlock (H.map (AddAut.conj g).toMul.toAddMonoidHom) (g +ᵥ B) := by
  rw [AddAction.isBlock_iff_vadd_eq_or_disjoint]
  intro h'
  obtain ⟨h, hH, hh⟩ := AddSubgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [AddEquiv.coe_toAddMonoidHom, AddAut.conj_apply] at hh
  suffices h' +ᵥ (g +ᵥ B) = g +ᵥ (h +ᵥ B) by
    simp only [this]
    apply (hB.vadd_eq_or_disjoint ⟨h, hH⟩).imp
    · intro hB'; congr
    · exact Set.disjoint_image_of_injective (AddAction.injective g)
  suffices (h' : G) +ᵥ (g +ᵥ B) = g +ᵥ (h +ᵥ B) by
    exact this
  rw [← hh, vadd_vadd, vadd_vadd]
  simp

theorem IsBlock.of_subgroup_of_conjugate {H : Subgroup G} (hB : IsBlock H B) (g : G) :
    IsBlock (H.map (MulAut.conj g).toMonoidHom) (g • B) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    apply (hB.smul_eq_or_disjoint ⟨h, hH⟩).imp
    · intro; congr
    · exact Set.disjoint_image_of_injective (MulAction.injective g)
  suffices (h' : G) • g • B = g • h • B by
    rw [← this]; rfl
  rw [← hh, smul_smul (g * h * g⁻¹) g B, smul_smul g h B, inv_mul_cancel_right]

/-- A translate of a block is a block -/
theorem _root_.AddAction.IsBlock.translate
    {G : Type*} [AddGroup G] {X : Type*} [AddAction G X] (B : Set X)
    (g : G) (hB : AddAction.IsBlock G B) :
    AddAction.IsBlock G (g +ᵥ B) := by
  rw [← AddAction.isBlock_top] at hB ⊢
  rw [← AddSubgroup.map_comap_eq_self_of_surjective (G := G) ?_ ⊤]
  · apply AddAction.IsBlock.of_addSubgroup_of_conjugate
    rwa [AddSubgroup.comap_top]
  · exact (AddAut.conj g).surjective

/-- A translate of a block is a block -/
@[to_additive existing]
theorem IsBlock.translate (g : G) (hB : IsBlock G B) :
    IsBlock G (g • B) := by
  rw [← isBlock_top] at hB ⊢
  rw [← Subgroup.map_comap_eq_self_of_surjective
          (G := G) (f := MulAut.conj g) (MulAut.conj g).surjective ⊤]
  apply IsBlock.of_subgroup_of_conjugate
  rwa [Subgroup.comap_top]

variable (G) in
/-- For `SMul G X`, a block system of `X` is a partition of `X` into blocks
for the action of `G` -/
@[to_additive /-- For `VAdd G X`, a block system of `X` is a partition of `X` into blocks
for the additive action of `G` -/]
def IsBlockSystem (ℬ : Set (Set X)) := Setoid.IsPartition ℬ ∧ ∀ ⦃B⦄, B ∈ ℬ → IsBlock G B

/-- Translates of a block form a block system -/
@[to_additive /-- Translates of a block form a block system -/]
theorem IsBlock.isBlockSystem [hGX : MulAction.IsPretransitive G X]
    (hB : IsBlock G B) (hBe : B.Nonempty) :
    IsBlockSystem G (Set.range fun g : G => g • B) := by
  refine ⟨⟨?nonempty, ?cover⟩, ?mem_blocks⟩
  case mem_blocks => rintro B' ⟨g, rfl⟩; exact hB.translate g
  · simp only [Set.mem_range, not_exists]
    intro g hg
    apply hBe.ne_empty
    simpa only [Set.smul_set_eq_empty] using hg
  · intro a
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe
    obtain ⟨g, rfl⟩ := exists_smul_eq G b a
    use g • B
    simp only [Set.smul_mem_smul_set_iff, hb, Set.mem_range,
      exists_apply_eq_apply, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff, true_and]
    exact fun g' ha ↦ hB.smul_eq_smul_of_nonempty ⟨g • b, ha, ⟨b, hb, rfl⟩⟩

section Normal

@[to_additive]
lemma smul_orbit_eq_orbit_smul (N : Subgroup G) [nN : N.Normal] (a : X) (g : G) :
    g • orbit N a = orbit N (g • a) := by
  simp only [orbit, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g * k * g⁻¹, nN.conj_mem k hk g⟩
    simp only [Subgroup.mk_smul]
    rw [smul_smul, inv_mul_cancel_right, ← smul_smul]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    use ⟨g⁻¹ * k * g, nN.conj_mem' k hk g⟩
    simp only [Subgroup.mk_smul]
    simp only [← smul_smul, smul_inv_smul]

/-- An orbit of a normal subgroup is a block -/
@[to_additive /-- An orbit of a normal subgroup is a block -/]
theorem IsBlock.orbit_of_normal {N : Subgroup G} [N.Normal] (a : X) :
    IsBlock G (orbit N a) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  rw [smul_orbit_eq_orbit_smul]
  apply orbit.eq_or_disjoint

/-- The orbits of a normal subgroup form a block system -/
@[to_additive /-- The orbits of a normal subgroup form a block system -/]
theorem IsBlockSystem.of_normal {N : Subgroup G} [N.Normal] :
    IsBlockSystem G (Set.range fun a : X => orbit N a) := by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact .orbit_of_normal a

section Group
variable {S H : Type*} [Group H] [SetLike S H] [SubgroupClass S H] {s : S} {a : G}

/-!
Annoyingly, it seems like the following two lemmas cannot be unified.
-/

section Left
variable [MulAction G H] [IsScalarTower G H H]

/-- See `MulAction.isBlock_subgroup'` for a version that works for the right action of a group on
itself. -/
@[to_additive /-- See `AddAction.isBlock_subgroup'` for a version that works for the right action
of a group on itself. -/]
lemma isBlock_subgroup : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe_set hc, smul_coe_set hd]

end Left

section Right
variable [MulAction G H] [IsScalarTower G Hᵐᵒᵖ H]

open MulOpposite

/-- See `MulAction.isBlock_subgroup` for a version that works for the left action of a group on
itself. -/
@[to_additive /-- See `AddAction.isBlock_subgroup` for a version that works for the left action
of a group on itself. -/]
lemma isBlock_subgroup' : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc, ← smul_assoc, ← op_smul, ← hcd, op_smul, smul_assoc, op_smul_coe_set hc,
    op_smul_coe_set hd]

end Right
end Group

end Normal

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `block_stabilizerOrderIso` between
  - blocks of `MulAction G X` containing a point `a ∈ X`,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/
@[to_additive /-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/]
theorem IsBlock.of_orbit {H : Subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
    IsBlock G (MulAction.orbit H a) := by
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨-, ⟨-, ⟨h₁, rfl⟩, h⟩, h₂, rfl⟩
  suffices g ∈ H by
    rw [← Subgroup.coe_mk H g this, ← H.toSubmonoid.smul_def, smul_orbit (⟨g, this⟩ : H) a]
  rw [← mul_mem_cancel_left h₂⁻¹.2, ← mul_mem_cancel_right h₁.2]
  apply hH
  simpa only [mem_stabilizer_iff, InvMemClass.coe_inv, mul_smul, inv_smul_eq_iff]

/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/
@[to_additive
/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/]
theorem IsBlock.stabilizer_le (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    stabilizer G a ≤ stabilizer G B :=
  fun g hg ↦ hB.smul_eq_of_nonempty ⟨a, by rwa [← hg, smul_mem_smul_set_iff], ha⟩

/-- A block containing `a` is the orbit of `a` under its stabilizer -/
@[to_additive /-- A block containing `a` is the orbit of `a` under its stabilizer -/]
theorem IsBlock.orbit_stabilizer_eq [IsPretransitive G X] (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    MulAction.orbit (stabilizer G B) a = B := by
  ext x
  constructor
  · rintro ⟨⟨k, k_mem⟩, rfl⟩
    simp only [Subgroup.mk_smul]
    rw [← k_mem, Set.smul_mem_smul_set_iff]
    exact ha
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    exact ⟨⟨k, hB.smul_eq_of_mem ha hx⟩, rfl⟩

/-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/
@[to_additive
  /-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/]
theorem stabilizer_orbit_eq {a : X} {H : Subgroup G} (hH : stabilizer G a ≤ H) :
    stabilizer G (orbit H a) = H := by
  ext g
  constructor
  · intro hg
    obtain ⟨-, ⟨b, rfl⟩, h⟩ := hg.symm ▸ mem_orbit_self a
    simp_rw [H.toSubmonoid.smul_def, ← mul_smul, ← mem_stabilizer_iff] at h
    exact (mul_mem_cancel_right b.2).mp (hH h)
  · intro hg
    rw [mem_stabilizer_iff, ← Subgroup.coe_mk H g hg, ← Submonoid.smul_def (S := H.toSubmonoid)]
    apply smul_orbit (G := H)

variable (G)

/-- Order equivalence between blocks in `X` containing a point `a`
and subgroups of `G` containing the stabilizer of `a` (Wielandt, th. 7.5) -/
@[to_additive
/-- Order equivalence between blocks in `X` containing a point `a`
and subgroups of `G` containing the stabilizer of `a` (Wielandt, th. 7.5) -/]
def block_stabilizerOrderIso [htGX : IsPretransitive G X] (a : X) :
    { B : Set X // a ∈ B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a) where
  toFun := fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, hB.stabilizer_le ha⟩
  invFun := fun ⟨H, hH⟩ =>
    ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock.of_orbit hH⟩
  left_inv := fun ⟨_, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨_, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_orbit_eq hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Set.le_eq_subset]
    constructor
    · rintro hBB' b hb
      obtain ⟨k, rfl⟩ := htGX.exists_smul_eq a b
      suffices k ∈ stabilizer G B' by
        exact this.symm ▸ (Set.smul_mem_smul_set ha')
      exact hBB' (hB.smul_eq_of_mem ha hb)
    · intro hBB' g hgB
      apply hB'.smul_eq_of_mem ha'
      exact hBB' <| hgB.symm ▸ (Set.smul_mem_smul_set ha)

/-- The type of blocks for a group action containing a given element -/
@[to_additive
/-- The type of blocks for an additive group action containing a given element -/]
abbrev BlockMem (a : X) : Type _ := {B : Set X // a ∈ B ∧ IsBlock G B}

namespace BlockMem

/-- The type of blocks for a group action containing a given element is a bounded order. -/
@[to_additive /-- The type of blocks for an additive group action containing a given element is a
bounded order. -/]
instance (a : X) : BoundedOrder (BlockMem G a) where
  top := ⟨Set.univ, Set.mem_univ a, .univ⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, le_eq_subset, subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, IsBlock.singleton⟩
  bot_le := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, Set.le_eq_subset, Set.singleton_subset_iff]
    exact ha

@[to_additive (attr := simp, norm_cast)]
theorem coe_top (a : X) :
    ((⊤ : BlockMem G a) : Set X) = Set.univ :=
  rfl

@[to_additive (attr := simp, norm_cast)]
theorem coe_bot (a : X) :
    ((⊥ : BlockMem G a) : Set X) = {a} :=
  rfl

@[to_additive]
instance [Nontrivial X] (a : X) : Nontrivial (BlockMem G a) := by
  rw [nontrivial_iff]
  use ⊥, ⊤
  intro h
  rw [← Subtype.coe_inj] at h
  simp only [coe_top, coe_bot] at h
  obtain ⟨b, hb⟩ := exists_ne a
  apply hb
  rw [← Set.mem_singleton_iff, h]
  apply Set.mem_univ

end BlockMem

end Stabilizer

section Finite

namespace IsBlock

variable [IsPretransitive G X] {B : Set X}

@[to_additive]
theorem ncard_block_eq_relIndex (hB : IsBlock G B) {x : X} (hx : x ∈ B) :
    B.ncard = (stabilizer G x).relIndex (stabilizer G B) := by
  have key : (stabilizer G x).subgroupOf (stabilizer G B) = stabilizer (stabilizer G B) x := by
    ext; rfl
  rw [Subgroup.relIndex, key, index_stabilizer, hB.orbit_stabilizer_eq hx]

@[deprecated (since := "2025-08-12")] alias ncard_block_eq_relindex := ncard_block_eq_relIndex

/-- The cardinality of the ambient space is the product of the cardinality of a block
  by the cardinality of the set of translates of that block -/
@[to_additive
  /-- The cardinality of the ambient space is the product of the cardinality of a block
  by the cardinality of the set of translates of that block -/]
theorem ncard_block_mul_ncard_orbit_eq (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B * Set.ncard (orbit G B) = Nat.card X := by
  obtain ⟨x, hx⟩ := hB_ne
  rw [ncard_block_eq_relIndex hB hx, ← index_stabilizer,
      Subgroup.relIndex_mul_index (hB.stabilizer_le hx), index_stabilizer_of_transitive]

/-- The cardinality of a block divides the cardinality of the ambient type -/
@[to_additive /-- The cardinality of a block divides the cardinality of the ambient type -/]
theorem ncard_dvd_card (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B ∣ Nat.card X :=
  Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

/-- A too large block is equal to `univ` -/
@[to_additive /-- A too large block is equal to `univ` -/]
theorem eq_univ_of_card_lt [hX : Finite X] (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) :
    B = Set.univ := by
  rcases Set.eq_empty_or_nonempty B with rfl | hB_ne
  · simp only [Set.ncard_empty, zero_mul, not_lt_zero'] at hB'
  have key := hB.ncard_block_mul_ncard_orbit_eq hB_ne
  rw [← key, mul_lt_mul_iff_of_pos_left (by rwa [Set.ncard_pos])] at hB'
  interval_cases (orbit G B).ncard
  · rw [mul_zero, eq_comm, Nat.card_eq_zero, or_iff_left hX.not_infinite] at key
    exact (IsEmpty.exists_iff.mp hB_ne).elim
  · rw [mul_one, ← Set.ncard_univ] at key
    rw [Set.eq_of_subset_of_ncard_le (Set.subset_univ B) key.ge]

/-- If a block has too many translates, then it is a (sub)singleton -/
@[to_additive /-- If a block has too many translates, then it is a (sub)singleton -/]
theorem subsingleton_of_card_lt [Finite X] (hB : IsBlock G B)
    (hB' : Nat.card X < 2 * Set.ncard (orbit G B)) :
    B.Subsingleton := by
  suffices Set.ncard B < 2 by
    rw [Nat.lt_succ_iff, Set.ncard_le_one_iff_eq] at this
    cases this with
    | inl h => rw [h]; exact Set.subsingleton_empty
    | inr h =>
      obtain ⟨a, ha⟩ := h; rw [ha]; exact Set.subsingleton_singleton
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; simp
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h, lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb ↦ hB' (Nat.mul_le_mul_right _ hb)

/- The assumption `B.Finite` is necessary :
  For G = ℤ acting on itself, a = 0 and B = ℕ, the translates `k • B` of the statement
  are just `k + ℕ`, for `k ≤ 0`, and the corresponding intersection is `ℕ`, which is not a block.
  (Remark by Thomas Browning) -/
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3). -/
@[to_additive
  /-- The intersection of the translates of a *finite* subset which contain a given point
  is a block (Wielandt, th. 7.3). -/]
theorem of_subset (a : X) (hfB : B.Finite) :
    IsBlock G (⋂ (k : G) (_ : a ∈ k • B), k • B) := by
  let B' := ⋂ (k : G) (_ : a ∈ k • B), k • B
  rcases Set.eq_empty_or_nonempty B with hfB_e | hfB_ne
  · simp [hfB_e]
  have hB'₀ : ∀ (k : G) (_ : a ∈ k • B), B' ≤ k • B := by
    intro k hk
    exact Set.biInter_subset_of_mem hk
  have hfB' : B'.Finite := by
    obtain ⟨b, hb : b ∈ B⟩ := hfB_ne
    obtain ⟨k, hk : k • b = a⟩ := exists_smul_eq G b a
    apply Set.Finite.subset (Set.Finite.map _ hfB) (hB'₀ k ⟨b, hb, hk⟩)
  have hag : ∀ g : G, a ∈ g • B' → B' ≤ g • B' :=  by
    intro g hg x hx
    -- a = g • b; b ∈ B'; a ∈ k • B → b ∈ k • B
    simp only [B', Set.mem_iInter, Set.mem_smul_set_iff_inv_smul_mem,
      smul_smul, ← mul_inv_rev] at hg hx ⊢
    exact fun _ ↦ hx _ ∘ hg _
  have hag' (g : G) (hg : a ∈ g • B') : B' = g • B' := by
    rw [eq_comm, ← mem_stabilizer_iff, mem_stabilizer_set_iff_subset_smul_set hfB']
    exact hag g hg
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩
  obtain ⟨k : G, hk : k • a = b⟩ := exists_smul_eq G a b
  have hak : a ∈ k⁻¹ • B' := by
    refine ⟨b, hb, ?_⟩
    simp only [← hk, inv_smul_smul]
  have hagk : a ∈ (k⁻¹ * g) • B' := by
    rw [mul_smul, Set.mem_smul_set_iff_inv_smul_mem, inv_inv, hk]
    exact hb'
  have hkB' : B' = k⁻¹ • B' := hag' k⁻¹ hak
  have hgkB' : B' = (k⁻¹ * g) • B' := hag' (k⁻¹ * g) hagk
  rw [mul_smul] at hgkB'
  rw [← smul_eq_iff_eq_inv_smul] at hkB' hgkB'
  rw [← hgkB', hkB']

end IsBlock

end Finite

end Group

end MulAction
