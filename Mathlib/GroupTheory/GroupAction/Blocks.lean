/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.Setoid.Partition
public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.IntervalCases

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `MonoidAction.IsBlock G B` states that `B : Set X` is a block,
  which means that the sets `g • B`, for `g ∈ G`, are equal or disjoint.
  Under `Group G` and `MonoidAction G X`, this is equivalent to the classical
  definition `MonoidAction.IsBlock.def_one`

- a bunch of lemmas that give examples of “trivial” blocks : ⊥, ⊤, singletons,
  and non-trivial blocks: orbit of the group, orbit of a normal subgroup…

The non-existence of nontrivial blocks is the definition of primitive actions.

## Results for actions on finite sets

- `MonoidAction.IsBlock.ncard_block_mul_ncard_orbit_eq` : The cardinality of a block
  multiplied by the number of its translates is the cardinal of the ambient type

- `MonoidAction.IsBlock.eq_univ_of_card_lt` : a too large block is equal to `Set.univ`

- `MonoidAction.IsBlock.subsingleton_of_card_lt` : a too small block is a subsingleton

- `MonoidAction.IsBlock.of_subset` : the intersections of the translates of a finite subset
  that contain a given point is a block

- `MonoidAction.BlockMem` : the type of blocks containing a given element

- `MonoidAction.BlockMem.instBoundedOrder` :
  the type of blocks containing a given element is a bounded order.

## References

We follow [Wielandt-1964].

-/

@[expose] public section

open Set
open scoped Pointwise

namespace MonoidAction

section orbits

variable {G : Type*} [Group G] {X : Type*} [MonoidAction G X]

@[to_additive]
theorem orbit.eq_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) := by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp +contextual
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, eq_comm, implies_true]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbit.eq_or_disjoint := orbit.eq_or_disjoint
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit.eq_or_disjoint := _root_.AddMonoidAction.orbit.eq_or_disjoint

@[to_additive]
theorem orbit.pairwiseDisjoint :
    (Set.range fun x : X => orbit G x).PairwiseDisjoint id := by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.orbit.pairwiseDisjoint := orbit.pairwiseDisjoint
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.orbit.pairwiseDisjoint := _root_.AddMonoidAction.orbit.pairwiseDisjoint

/-- Orbits of an element form a partition -/
@[to_additive /-- Orbits of an element form a partition -/]
theorem IsPartition.of_orbits :
    Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MonoidAction.nonempty_orbit a).ne_empty ha

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsPartition.of_orbits := IsPartition.of_orbits
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsPartition.of_orbits := _root_.AddMonoidAction.IsPartition.of_orbits

end orbits

section SMul

variable (G : Type*) {X : Type*} [SMul G X] {B : Set X} {a : X}

-- Change terminology to IsFullyInvariant?
/-- A set `B` is a `G`-fixed block if `g • B = B` for all `g : G`. -/
@[to_additive /-- A set `B` is a `G`-fixed block if `g +ᵥ B = B` for all `g : G`. -/]
def IsFixedBlock (B : Set X) := ∀ g : G, g • B = B

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsFixedBlock := IsFixedBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsFixedBlock := _root_.AddMonoidAction.IsFixedBlock

/-- A set `B` is a `G`-invariant block if `g • B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A set `B` is a `G`-invariant block if `g +ᵥ B ⊆ B` for all `g : G`.

Note: It is not necessarily a block when the action is not by a group. -/]
def IsInvariantBlock (B : Set X) := ∀ g : G, g • B ⊆ B

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsInvariantBlock := IsInvariantBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsInvariantBlock := _root_.AddMonoidAction.IsInvariantBlock

section IsTrivialBlock

/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/
@[to_additive
/-- A trivial block is a `Set X` which is either a subsingleton or `univ`.

Note: It is not necessarily a block when the action is not by a group. -/]
def IsTrivialBlock (B : Set X) := B.Subsingleton ∨ B = univ

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsTrivialBlock := IsTrivialBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsTrivialBlock := _root_.AddMonoidAction.IsTrivialBlock

variable {M α N β : Type*}

section monoid

variable [Monoid M] [MonoidAction M α] [Monoid N] [MonoidAction N β]

@[to_additive]
theorem IsTrivialBlock.image {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Surjective f) {B : Set α} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f '' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; apply Set.Subsingleton.image hB
  · apply Or.intro_right; rw [hB]
    simp only [Set.image_univ, Set.range_eq_univ, hf]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsTrivialBlock.image := IsTrivialBlock.image
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsTrivialBlock.image := _root_.AddMonoidAction.IsTrivialBlock.image

@[to_additive]
theorem IsTrivialBlock.preimage {φ : M → N} {f : α →ₑ[φ] β}
    (hf : Function.Injective f) {B : Set β} (hB : IsTrivialBlock B) :
    IsTrivialBlock (f ⁻¹' B) := by
  obtain hB | hB := hB
  · apply Or.intro_left; exact Set.Subsingleton.preimage hB hf
  · apply Or.intro_right; simp only [hB]; apply Set.preimage_univ

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsTrivialBlock.preimage := IsTrivialBlock.preimage
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsTrivialBlock.preimage := _root_.AddMonoidAction.IsTrivialBlock.preimage

end monoid

variable [Group M] [MonoidAction M α] [Monoid N] [MonoidAction N β]

@[to_additive]
theorem IsTrivialBlock.smul {B : Set α} (hB : IsTrivialBlock B) (g : M) :
    IsTrivialBlock (g • B) := by
  cases hB with
  | inl h =>
    left
    exact (Function.Injective.subsingleton_image_iff (MonoidAction.injective g)).mpr h
  | inr h =>
    right
    rw [h, ← Set.image_smul, Set.image_univ_of_surjective (MonoidAction.surjective g)]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsTrivialBlock.smul := IsTrivialBlock.smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsTrivialBlock.vadd := _root_.AddMonoidAction.IsTrivialBlock.vadd

@[to_additive]
theorem IsTrivialBlock.smul_iff {B : Set α} (g : M) :
    IsTrivialBlock (g • B) ↔ IsTrivialBlock B := by
  constructor
  · intro H
    convert! IsTrivialBlock.smul H g⁻¹
    simp only [inv_smul_smul]
  · intro H
    exact IsTrivialBlock.smul H g

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsTrivialBlock.smul_iff := IsTrivialBlock.smul_iff
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsTrivialBlock.vadd_iff := _root_.AddMonoidAction.IsTrivialBlock.vadd_iff

end IsTrivialBlock

/-- A set `B` is a `G`-block iff the sets of the form `g • B` are pairwise equal or disjoint. -/
@[to_additive
/-- A set `B` is a `G`-block iff the sets of the form `g +ᵥ B` are pairwise equal or disjoint. -/]
def IsBlock (B : Set X) := ∀ ⦃g₁ g₂ : G⦄, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B)

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock := IsBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock := _root_.AddMonoidAction.IsBlock

variable {G} {s : Set G} {g g₁ g₂ : G}

@[to_additive]
lemma isBlock_iff_smul_eq_smul_of_nonempty :
    IsBlock G B ↔ ∀ ⦃g₁ g₂ : G⦄, (g₁ • B ∩ g₂ • B).Nonempty → g₁ • B = g₂ • B := by
  simp_rw [IsBlock, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_smul_eq_smul_of_nonempty := isBlock_iff_smul_eq_smul_of_nonempty
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_vadd_eq_vadd_of_nonempty :=
  _root_.AddMonoidAction.isBlock_iff_vadd_eq_vadd_of_nonempty

@[to_additive]
lemma isBlock_iff_pairwiseDisjoint_range_smul :
    IsBlock G B ↔ (range fun g : G ↦ g • B).PairwiseDisjoint id := pairwiseDisjoint_range_iff.symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_pairwiseDisjoint_range_smul :=
  isBlock_iff_pairwiseDisjoint_range_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_pairwiseDisjoint_range_vadd :=
  _root_.AddMonoidAction.isBlock_iff_pairwiseDisjoint_range_vadd

@[to_additive]
lemma isBlock_iff_smul_eq_smul_or_disjoint :
    IsBlock G B ↔ ∀ g₁ g₂ : G, g₁ • B = g₂ • B ∨ Disjoint (g₁ • B) (g₂ • B) :=
  forall₂_congr fun _ _ ↦ or_iff_not_imp_left.symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_smul_eq_smul_or_disjoint := isBlock_iff_smul_eq_smul_or_disjoint
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_vadd_eq_vadd_or_disjoint :=
  _root_.AddMonoidAction.isBlock_iff_vadd_eq_vadd_or_disjoint

@[to_additive]
lemma IsBlock.smul_eq_smul_of_subset (hB : IsBlock G B) (hg : g₁ • B ⊆ g₂ • B) :
    g₁ • B = g₂ • B := by
  by_contra! hg'
  obtain rfl : B = ∅ := by simpa using (hB hg').eq_bot_of_le hg
  simp at hg'

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.smul_eq_smul_of_subset := IsBlock.smul_eq_smul_of_subset
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.vadd_eq_vadd_of_subset :=
  _root_.AddMonoidAction.IsBlock.vadd_eq_vadd_of_subset

@[to_additive]
lemma IsBlock.not_smul_set_ssubset_smul_set (hB : IsBlock G B) : ¬ g₁ • B ⊂ g₂ • B :=
  fun hab ↦ hab.ne <| hB.smul_eq_smul_of_subset hab.subset

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.not_smul_set_ssubset_smul_set :=
  IsBlock.not_smul_set_ssubset_smul_set
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.not_vadd_set_ssubset_vadd_set :=
  _root_.AddMonoidAction.IsBlock.not_vadd_set_ssubset_vadd_set

@[to_additive]
lemma IsBlock.disjoint_smul_set_smul (hB : IsBlock G B) (hgs : ¬ g • B ⊆ s • B) :
    Disjoint (g • B) (s • B) := by
  rw [← iUnion_smul_set, disjoint_iUnion₂_right]
  exact fun b hb ↦ hB fun h ↦ hgs <| h.trans_subset <| smul_set_subset_smul hb

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.disjoint_smul_set_smul := IsBlock.disjoint_smul_set_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.disjoint_vadd_set_vadd :=
  _root_.AddMonoidAction.IsBlock.disjoint_vadd_set_vadd

@[to_additive]
lemma IsBlock.disjoint_smul_smul_set (hB : IsBlock G B) (hgs : ¬ g • B ⊆ s • B) :
    Disjoint (s • B) (g • B) := (hB.disjoint_smul_set_smul hgs).symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.disjoint_smul_smul_set := IsBlock.disjoint_smul_smul_set
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.disjoint_vadd_vadd_set :=
  _root_.AddMonoidAction.IsBlock.disjoint_vadd_vadd_set

@[to_additive]
alias ⟨IsBlock.smul_eq_smul_of_nonempty, _⟩ := isBlock_iff_smul_eq_smul_of_nonempty
@[to_additive]
alias ⟨IsBlock.pairwiseDisjoint_range_smul, _⟩ := isBlock_iff_pairwiseDisjoint_range_smul
@[to_additive]
alias ⟨IsBlock.smul_eq_smul_or_disjoint, _⟩ := isBlock_iff_smul_eq_smul_or_disjoint

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.pairwiseDisjoint_range_smul := IsBlock.pairwiseDisjoint_range_smul
@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.smul_eq_smul_of_nonempty := IsBlock.smul_eq_smul_of_nonempty
@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.smul_eq_smul_or_disjoint := IsBlock.smul_eq_smul_or_disjoint
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.pairwiseDisjoint_range_vadd :=
  _root_.AddMonoidAction.IsBlock.pairwiseDisjoint_range_vadd
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.vadd_eq_vadd_of_nonempty :=
  _root_.AddMonoidAction.IsBlock.vadd_eq_vadd_of_nonempty
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.vadd_eq_vadd_or_disjoint :=
  _root_.AddMonoidAction.IsBlock.vadd_eq_vadd_or_disjoint

/-- A fixed block is a block. -/
@[to_additive /-- A fixed block is a block. -/]
lemma IsFixedBlock.isBlock (hfB : IsFixedBlock G B) : IsBlock G B := by simp [IsBlock, hfB _]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsFixedBlock.isBlock := IsFixedBlock.isBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsFixedBlock.isBlock := _root_.AddMonoidAction.IsFixedBlock.isBlock

/-- The empty set is a block. -/
@[to_additive (attr := simp) /-- The empty set is a block. -/]
lemma IsBlock.empty : IsBlock G (∅ : Set X) := by simp [IsBlock]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.empty := IsBlock.empty
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.empty := _root_.AddMonoidAction.IsBlock.empty

/-- A singleton is a block. -/
@[to_additive /-- A singleton is a block. -/]
lemma IsBlock.singleton : IsBlock G ({a} : Set X) := by simp [IsBlock]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.singleton := IsBlock.singleton
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.singleton := _root_.AddMonoidAction.IsBlock.singleton

/-- Subsingletons are (trivial) blocks. -/
@[to_additive /-- Subsingletons are (trivial) blocks. -/]
lemma IsBlock.of_subsingleton (hB : B.Subsingleton) : IsBlock G B :=
  hB.induction_on .empty fun _ ↦ .singleton

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.of_subsingleton := IsBlock.of_subsingleton
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.of_subsingleton := _root_.AddMonoidAction.IsBlock.of_subsingleton

/-- A fixed block is an invariant block. -/
@[to_additive /-- A fixed block is an invariant block. -/]
lemma IsFixedBlock.isInvariantBlock (hB : IsFixedBlock G B) : IsInvariantBlock G B :=
  fun _ ↦ (hB _).le

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsFixedBlock.isInvariantBlock := IsFixedBlock.isInvariantBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsFixedBlock.isInvariantBlock :=
  _root_.AddMonoidAction.IsFixedBlock.isInvariantBlock

end SMul

section Monoid
variable {M X : Type*} [Monoid M] [MonoidAction M X] {B : Set X} {s : Set M}

@[to_additive]
lemma IsBlock.disjoint_smul_right (hB : IsBlock M B) (hs : ¬ B ⊆ s • B) : Disjoint B (s • B) := by
  simpa using hB.disjoint_smul_set_smul (g := 1) (by simpa using hs)

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.disjoint_smul_right := IsBlock.disjoint_smul_right
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.disjoint_vadd_right :=
  _root_.AddMonoidAction.IsBlock.disjoint_vadd_right

@[to_additive]
lemma IsBlock.disjoint_smul_left (hB : IsBlock M B) (hs : ¬ B ⊆ s • B) : Disjoint (s • B) B :=
  (hB.disjoint_smul_right hs).symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.disjoint_smul_left := IsBlock.disjoint_smul_left
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.disjoint_vadd_left :=
  _root_.AddMonoidAction.IsBlock.disjoint_vadd_left

end Monoid

section Group

variable {G : Type*} [Group G] {X : Type*} [MonoidAction G X] {B : Set X}

@[to_additive]
lemma isBlock_iff_disjoint_smul_of_ne :
    IsBlock G B ↔ ∀ ⦃g : G⦄, g • B ≠ B → Disjoint (g • B) B := by
  refine ⟨fun hB g ↦ by simpa using hB (g₂ := 1), fun hB g₁ g₂ h ↦ ?_⟩
  simp only [disjoint_smul_set_right, ne_eq, ← inv_smul_eq_iff, smul_smul] at h ⊢
  exact hB h

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_disjoint_smul_of_ne := isBlock_iff_disjoint_smul_of_ne
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_disjoint_vadd_of_ne :=
  _root_.AddMonoidAction.isBlock_iff_disjoint_vadd_of_ne

@[to_additive]
lemma isBlock_iff_smul_eq_of_nonempty :
    IsBlock G B ↔ ∀ ⦃g : G⦄, (g • B ∩ B).Nonempty → g • B = B := by
  simp_rw [isBlock_iff_disjoint_smul_of_ne, ← not_disjoint_iff_nonempty_inter, not_imp_comm]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_smul_eq_of_nonempty := isBlock_iff_smul_eq_of_nonempty
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_vadd_eq_of_nonempty :=
  _root_.AddMonoidAction.isBlock_iff_vadd_eq_of_nonempty

@[to_additive]
lemma isBlock_iff_smul_eq_or_disjoint :
    IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B :=
  isBlock_iff_disjoint_smul_of_ne.trans <| forall_congr' fun _ ↦ or_iff_not_imp_left.symm

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_smul_eq_or_disjoint := isBlock_iff_smul_eq_or_disjoint
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_vadd_eq_or_disjoint :=
  _root_.AddMonoidAction.isBlock_iff_vadd_eq_or_disjoint

@[to_additive]
lemma isBlock_iff_smul_eq_of_mem :
    IsBlock G B ↔ ∀ ⦃g : G⦄ ⦃a : X⦄, a ∈ B → g • a ∈ B → g • B = B := by
  simp [isBlock_iff_smul_eq_of_nonempty, Set.Nonempty, mem_smul_set]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_iff_smul_eq_of_mem := isBlock_iff_smul_eq_of_mem
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_iff_vadd_eq_of_mem :=
  _root_.AddMonoidAction.isBlock_iff_vadd_eq_of_mem

@[to_additive] alias ⟨IsBlock.disjoint_smul_of_ne, _⟩ := isBlock_iff_disjoint_smul_of_ne
@[to_additive] alias ⟨IsBlock.smul_eq_of_nonempty, _⟩ := isBlock_iff_smul_eq_of_nonempty
@[to_additive] alias ⟨IsBlock.smul_eq_or_disjoint, _⟩ := isBlock_iff_smul_eq_or_disjoint
@[to_additive] alias ⟨IsBlock.smul_eq_of_mem, _⟩ := isBlock_iff_smul_eq_of_mem

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.disjoint_smul_of_ne := IsBlock.disjoint_smul_of_ne
@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.smul_eq_of_mem := IsBlock.smul_eq_of_mem
@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.smul_eq_of_nonempty := IsBlock.smul_eq_of_nonempty
@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.smul_eq_or_disjoint := IsBlock.smul_eq_or_disjoint
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.disjoint_vadd_of_ne :=
  _root_.AddMonoidAction.IsBlock.disjoint_vadd_of_ne
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.vadd_eq_of_mem := _root_.AddMonoidAction.IsBlock.vadd_eq_of_mem
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.vadd_eq_of_nonempty :=
  _root_.AddMonoidAction.IsBlock.vadd_eq_of_nonempty
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.vadd_eq_or_disjoint :=
  _root_.AddMonoidAction.IsBlock.vadd_eq_or_disjoint

-- TODO: Generalise to `SubgroupClass`
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/
@[to_additive
/-- If `B` is a `G`-block, then it is also a `H`-block for any subgroup `H` of `G`. -/]
lemma IsBlock.subgroup {H : Subgroup G} (hB : IsBlock G B) : IsBlock H B := fun _ _ h ↦ hB h

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.subgroup := IsBlock.subgroup
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.addSubgroup := _root_.AddMonoidAction.IsBlock.addSubgroup

/-- A block of a group action is invariant iff it is fixed. -/
@[to_additive /-- A block of a group action is invariant iff it is fixed. -/]
lemma isInvariantBlock_iff_isFixedBlock : IsInvariantBlock G B ↔ IsFixedBlock G B :=
  ⟨fun hB g ↦ (hB g).antisymm <| subset_smul_set_iff.2 <| hB _, IsFixedBlock.isInvariantBlock⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isInvariantBlock_iff_isFixedBlock := isInvariantBlock_iff_isFixedBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isInvariantBlock_iff_isFixedBlock :=
  _root_.AddMonoidAction.isInvariantBlock_iff_isFixedBlock

/-- An invariant block of a group action is a fixed block. -/
@[to_additive /-- An invariant block of a group action is a fixed block. -/]
alias ⟨IsInvariantBlock.isFixedBlock, _⟩ := isInvariantBlock_iff_isFixedBlock

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsInvariantBlock.isFixedBlock := IsInvariantBlock.isFixedBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsInvariantBlock.isFixedBlock :=
  _root_.AddMonoidAction.IsInvariantBlock.isFixedBlock

/-- An invariant block of a group action is a block. -/
@[to_additive /-- An invariant block of a group action is a block. -/]
lemma IsInvariantBlock.isBlock (hB : IsInvariantBlock G B) : IsBlock G B := hB.isFixedBlock.isBlock

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsInvariantBlock.isBlock := IsInvariantBlock.isBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsInvariantBlock.isBlock := _root_.AddMonoidAction.IsInvariantBlock.isBlock

/-- The full set is a fixed block. -/
@[to_additive /-- The full set is a fixed block. -/]
lemma IsFixedBlock.univ : IsFixedBlock G (univ : Set X) := fun _ ↦ by simp

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsFixedBlock.univ := IsFixedBlock.univ
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsFixedBlock.univ := _root_.AddMonoidAction.IsFixedBlock.univ

/-- The full set is a block. -/
@[to_additive (attr := simp) /-- The full set is a block. -/]
lemma IsBlock.univ : IsBlock G (univ : Set X) := IsFixedBlock.univ.isBlock

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.univ := IsBlock.univ
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.univ := _root_.AddMonoidAction.IsBlock.univ

/-- The intersection of two blocks is a block. -/
@[to_additive /-- The intersection of two blocks is a block. -/]
lemma IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ ∩ B₂) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_inter] at h₁ h₂ ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  rw [h₁ ⟨a, ha₁.1, ha₂.1⟩, h₂ ⟨a, ha₁.2, ha₂.2⟩]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.inter := IsBlock.inter
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.inter := _root_.AddMonoidAction.IsBlock.inter

/-- An intersection of blocks is a block. -/
@[to_additive /-- An intersection of blocks is a block. -/]
lemma IsBlock.iInter {ι : Sort*} {B : ι → Set X} (hB : ∀ i, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  simp only [isBlock_iff_smul_eq_smul_of_nonempty, smul_set_iInter] at hB ⊢
  rintro g₁ g₂ ⟨a, ha₁, ha₂⟩
  simp_rw [fun i ↦ hB i ⟨a, iInter_subset _ i ha₁, iInter_subset _ i ha₂⟩]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.iInter := IsBlock.iInter
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.iInter := _root_.AddMonoidAction.IsBlock.iInter

/-- A trivial block is a block. -/
@[to_additive /-- A trivial block is a block. -/]
lemma IsTrivialBlock.isBlock (hB : IsTrivialBlock B) : IsBlock G B := by
  obtain hB | rfl := hB
  · exact .of_subsingleton hB
  · exact .univ

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsTrivialBlock.isBlock := IsTrivialBlock.isBlock
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsTrivialBlock.isBlock := _root_.AddMonoidAction.IsTrivialBlock.isBlock

/-- An orbit is a fixed block. -/
@[to_additive /-- An orbit is a fixed block. -/]
protected lemma IsFixedBlock.orbit (a : X) : IsFixedBlock G (orbit G a) := (smul_orbit · a)

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsFixedBlock.orbit := _root_.MonoidAction.IsFixedBlock.orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsFixedBlock.orbit := _root_.AddMonoidAction.IsFixedBlock.orbit

/-- An orbit is a block. -/
@[to_additive /-- An orbit is a block. -/]
protected lemma IsBlock.orbit (a : X) : IsBlock G (orbit G a) := (IsFixedBlock.orbit a).isBlock

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.orbit := _root_.MonoidAction.IsBlock.orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.orbit := _root_.AddMonoidAction.IsBlock.orbit

@[to_additive]
lemma isBlock_top : IsBlock (⊤ : Subgroup G) B ↔ IsBlock G B :=
  Subgroup.topEquiv.toEquiv.forall_congr fun _ ↦ Subgroup.topEquiv.toEquiv.forall_congr_left

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.isBlock_top := isBlock_top
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_top := _root_.AddMonoidAction.isBlock_top

@[to_additive]
lemma IsBlock.preimage {H Y : Type*} [Group H] [MonoidAction H Y]
    {φ : H → G} (j : Y →ₑ[φ] X) (hB : IsBlock G B) :
    IsBlock H (j ⁻¹' B) := by
  rintro g₁ g₂ hg
  rw [← Group.preimage_smul_setₛₗ, ← Group.preimage_smul_setₛₗ] at hg ⊢
  exact (hB <| ne_of_apply_ne _ hg).preimage _

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.preimage := IsBlock.preimage
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.preimage := _root_.AddMonoidAction.IsBlock.preimage

@[to_additive]
theorem IsBlock.image {H Y : Type*} [SMul H Y] {φ : G → H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j) (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  simp only [IsBlock, hφ.forall, ← image_smul_setₛₗ]
  exact fun g₁ g₂ hg ↦ disjoint_image_of_injective hj <| hB <| ne_of_apply_ne _ hg

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.image := IsBlock.image
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.image := _root_.AddMonoidAction.IsBlock.image

@[to_additive]
theorem IsBlock.subtype_val_preimage {C : SubMulAction G X} (hB : IsBlock G B) :
    IsBlock G (Subtype.val ⁻¹' B : Set C) :=
  hB.preimage C.inclusion

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.subtype_val_preimage := IsBlock.subtype_val_preimage
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.subtype_val_preimage :=
  _root_.AddMonoidAction.IsBlock.subtype_val_preimage

@[to_additive]
theorem isBlock_subtypeVal {C : SubMulAction G X} {B : Set C} :
    IsBlock G (Subtype.val '' B : Set X) ↔ IsBlock G B := by
  refine forall₂_congr fun g₁ g₂ ↦ ?_
  rw [← SubMulAction.inclusion.coe_eq, ← image_smul_set, ← image_smul_set, ne_eq,
    Set.image_eq_image C.inclusion_injective, disjoint_image_iff C.inclusion_injective]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.isBlock_subtypeVal := isBlock_subtypeVal
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_subtypeVal := _root_.AddMonoidAction.isBlock_subtypeVal

@[to_additive]
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
    · exact Set.disjoint_image_of_injective (MonoidAction.injective g)
  suffices (h' : G) • g • B = g • h • B by
    rw [← this]; rfl
  rw [← hh, smul_smul (g * h * g⁻¹) g B, smul_smul g h B, inv_mul_cancel_right]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.of_subgroup_of_conjugate := IsBlock.of_subgroup_of_conjugate
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.of_addSubgroup_of_conjugate :=
  _root_.AddMonoidAction.IsBlock.of_addSubgroup_of_conjugate

/-- A translate of a block is a block -/
@[to_additive]
theorem IsBlock.translate (g : G) (hB : IsBlock G B) :
    IsBlock G (g • B) := by
  rw [← isBlock_top] at hB ⊢
  rw [← Subgroup.map_comap_eq_self_of_surjective
          (G := G) (f := MulAut.conj g) (MulAut.conj g).surjective ⊤]
  apply IsBlock.of_subgroup_of_conjugate
  rwa [Subgroup.comap_top]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.translate := IsBlock.translate
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.translate := _root_.AddMonoidAction.IsBlock.translate

variable (G) in
/-- For `SMul G X`, a block system of `X` is a partition of `X` into blocks
for the action of `G` -/
@[to_additive /-- For `VAdd G X`, a block system of `X` is a partition of `X` into blocks
for the additive action of `G` -/]
def IsBlockSystem (ℬ : Set (Set X)) := Setoid.IsPartition ℬ ∧ ∀ ⦃B⦄, B ∈ ℬ → IsBlock G B

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlockSystem := IsBlockSystem
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlockSystem := _root_.AddMonoidAction.IsBlockSystem

/-- Translates of a block form a block system -/
@[to_additive /-- Translates of a block form a block system -/]
theorem IsBlock.isBlockSystem [hGX : MonoidAction.IsPretransitive G X]
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

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.isBlockSystem := IsBlock.isBlockSystem
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.isBlockSystem := _root_.AddMonoidAction.IsBlock.isBlockSystem

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

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.smul_orbit_eq_orbit_smul := smul_orbit_eq_orbit_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.vadd_orbit_eq_orbit_vadd := _root_.AddMonoidAction.vadd_orbit_eq_orbit_vadd

/-- An orbit of a normal subgroup is a block -/
@[to_additive /-- An orbit of a normal subgroup is a block -/]
theorem IsBlock.orbit_of_normal {N : Subgroup G} [N.Normal] (a : X) :
    IsBlock G (orbit N a) := by
  rw [isBlock_iff_smul_eq_or_disjoint]
  intro g
  rw [smul_orbit_eq_orbit_smul]
  apply orbit.eq_or_disjoint

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.orbit_of_normal := IsBlock.orbit_of_normal
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.orbit_of_normal := _root_.AddMonoidAction.IsBlock.orbit_of_normal

/-- The orbits of a normal subgroup form a block system -/
@[to_additive /-- The orbits of a normal subgroup form a block system -/]
theorem IsBlockSystem.of_normal {N : Subgroup G} [N.Normal] :
    IsBlockSystem G (Set.range fun a : X => orbit N a) := by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact .orbit_of_normal a

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlockSystem.of_normal := IsBlockSystem.of_normal
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlockSystem.of_normal := _root_.AddMonoidAction.IsBlockSystem.of_normal

section Group
variable {S H : Type*} [Group H] [SetLike S H] [SubgroupClass S H] {s : S} {a : G}

/-!
Annoyingly, it seems like the following two lemmas cannot be unified.
-/

section Left
variable [MonoidAction G H] [IsScalarTower G H H]

/-- See `MonoidAction.isBlock_subgroup'` for a version that works for the right action of a group on
itself. -/
@[to_additive /-- See `AddMonoidAction.isBlock_subgroup'` for a version that works for the right
action
of a group on itself. -/]
lemma isBlock_subgroup : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← smul_coe_set hc, ← smul_assoc, ← hcd, smul_assoc, smul_coe_set hc, smul_coe_set hd]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.isBlock_subgroup := isBlock_subgroup
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_addSubgroup := _root_.AddMonoidAction.isBlock_addSubgroup

end Left

section Right
variable [MonoidAction G H] [IsScalarTower G Hᵐᵒᵖ H]

open MulOpposite

/-- See `MonoidAction.isBlock_subgroup` for a version that works for the left action of a group on
itself. -/
@[to_additive /-- See `AddMonoidAction.isBlock_subgroup` for a version that works for the left
action
of a group on itself. -/]
lemma isBlock_subgroup' : IsBlock G (s : Set H) := by
  simp only [IsBlock, disjoint_left]
  rintro a b hab _ ⟨c, hc, rfl⟩ ⟨d, hd, (hcd : b • d = a • c)⟩
  refine hab ?_
  rw [← op_smul_coe_set hc, ← smul_assoc, ← op_smul, ← hcd, op_smul, smul_assoc, op_smul_coe_set hc,
    op_smul_coe_set hd]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.isBlock_subgroup' := isBlock_subgroup'
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.isBlock_addSubgroup' := _root_.AddMonoidAction.isBlock_addSubgroup'

end Right
end Group

end Normal

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `block_stabilizerOrderIso` between
  - blocks of `MonoidAction G X` containing a point `a ∈ X`,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/
@[to_additive /-- The orbit of `a` under a subgroup containing the stabilizer of `a` is a block -/]
theorem IsBlock.of_orbit {H : Subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
    IsBlock G (MonoidAction.orbit H a) := by
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨-, ⟨-, ⟨h₁, rfl⟩, h⟩, h₂, rfl⟩
  suffices g ∈ H by
    rw [← Subgroup.coe_mk H g this, ← H.toSubmonoid.smul_def, smul_orbit (⟨g, this⟩ : H) a]
  rw [← mul_mem_cancel_left h₂⁻¹.2, ← mul_mem_cancel_right h₁.2]
  apply hH
  simpa only [mem_stabilizer_iff, InvMemClass.coe_inv, mul_smul, inv_smul_eq_iff]

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.of_orbit := IsBlock.of_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.of_orbit := _root_.AddMonoidAction.IsBlock.of_orbit

/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/
@[to_additive
/-- If `B` is a block containing `a`, then the stabilizer of `B` contains the stabilizer of `a` -/]
theorem IsBlock.stabilizer_le (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    stabilizer G a ≤ stabilizer G B :=
  fun g hg ↦ hB.smul_eq_of_nonempty ⟨a, by rwa [← hg, smul_mem_smul_set_iff], ha⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.stabilizer_le := IsBlock.stabilizer_le
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.stabilizer_le := _root_.AddMonoidAction.IsBlock.stabilizer_le

/-- A block containing `a` is the orbit of `a` under its stabilizer -/
@[to_additive /-- A block containing `a` is the orbit of `a` under its stabilizer -/]
theorem IsBlock.orbit_stabilizer_eq [IsPretransitive G X] (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    MonoidAction.orbit (stabilizer G B) a = B := by
  ext x
  constructor
  · rintro ⟨⟨k, k_mem⟩, rfl⟩
    simp only [Subgroup.mk_smul]
    rw [← k_mem, Set.smul_mem_smul_set_iff]
    exact ha
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    exact ⟨⟨k, hB.smul_eq_of_mem ha hx⟩, rfl⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.orbit_stabilizer_eq := IsBlock.orbit_stabilizer_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.orbit_stabilizer_eq :=
  _root_.AddMonoidAction.IsBlock.orbit_stabilizer_eq

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

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.stabilizer_orbit_eq := stabilizer_orbit_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.stabilizer_orbit_eq := _root_.AddMonoidAction.stabilizer_orbit_eq

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
    ⟨MonoidAction.orbit H a, MonoidAction.mem_orbit_self a, IsBlock.of_orbit hH⟩
  left_inv := fun ⟨_, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨_, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_orbit_eq hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk]
    constructor
    · rintro hBB' b hb
      obtain ⟨k, rfl⟩ := htGX.exists_smul_eq a b
      suffices k ∈ stabilizer G B' by
        exact this.symm ▸ (Set.smul_mem_smul_set ha')
      exact hBB' (hB.smul_eq_of_mem ha hb)
    · intro hBB' g hgB
      apply hB'.smul_eq_of_mem ha'
      exact hBB' <| hgB.symm ▸ (Set.smul_mem_smul_set ha)

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.block_stabilizerOrderIso := block_stabilizerOrderIso
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.block_stabilizerOrderIso := _root_.AddMonoidAction.block_stabilizerOrderIso

/-- The type of blocks for a group action containing a given element -/
@[to_additive
/-- The type of blocks for an additive group action containing a given element -/]
abbrev BlockMem (a : X) : Type _ := {B : Set X // a ∈ B ∧ IsBlock G B}

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.BlockMem := BlockMem
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.BlockMem := _root_.AddMonoidAction.BlockMem

namespace BlockMem

/-- The type of blocks for a group action containing a given element is a bounded order. -/
@[to_additive /-- The type of blocks for an additive group action containing a given element is a
bounded order. -/]
instance (a : X) : BoundedOrder (BlockMem G a) where
  top := ⟨Set.univ, Set.mem_univ a, .univ⟩
  le_top := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, subset_univ]
  bot := ⟨{a}, Set.mem_singleton a, IsBlock.singleton⟩
  bot_le := by
    rintro ⟨B, ha, hB⟩
    simp only [Subtype.mk_le_mk, Set.singleton_subset_iff]
    exact ha

@[to_additive (attr := simp, norm_cast)]
theorem coe_top (a : X) :
    ((⊤ : BlockMem G a) : Set X) = Set.univ :=
  rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.BlockMem.coe_top := coe_top
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.BlockMem.coe_top := _root_.AddMonoidAction.BlockMem.coe_top

@[to_additive (attr := simp, norm_cast)]
theorem coe_bot (a : X) :
    ((⊥ : BlockMem G a) : Set X) = {a} :=
  rfl

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.BlockMem.coe_bot := coe_bot
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.BlockMem.coe_bot := _root_.AddMonoidAction.BlockMem.coe_bot

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

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.ncard_block_eq_relIndex := ncard_block_eq_relIndex
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.ncard_block_eq_relIndex :=
  _root_.AddMonoidAction.IsBlock.ncard_block_eq_relIndex

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

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.ncard_block_mul_ncard_orbit_eq := ncard_block_mul_ncard_orbit_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.ncard_block_add_ncard_orbit_eq :=
  _root_.AddMonoidAction.IsBlock.ncard_block_add_ncard_orbit_eq

/-- The cardinality of a block divides the cardinality of the ambient type -/
@[to_additive /-- The cardinality of a block divides the cardinality of the ambient type -/]
theorem ncard_dvd_card (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B ∣ Nat.card X :=
  Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.ncard_dvd_card := ncard_dvd_card
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.ncard_dvd_card := _root_.AddMonoidAction.IsBlock.ncard_dvd_card

/-- A too large block is equal to `univ` -/
@[to_additive /-- A too large block is equal to `univ` -/]
theorem eq_univ_of_card_lt [hX : Finite X] (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) :
    B = Set.univ := by
  rcases Set.eq_empty_or_nonempty B with rfl | hB_ne
  · simp at hB'
  have key := hB.ncard_block_mul_ncard_orbit_eq hB_ne
  rw [← key, mul_lt_mul_iff_of_pos_left (by rwa [Set.ncard_pos])] at hB'
  interval_cases (orbit G B).ncard
  · rw [mul_zero, eq_comm, Nat.card_eq_zero, or_iff_left hX.not_infinite] at key
    exact (IsEmpty.exists_iff.mp hB_ne).elim
  · rw [mul_one, ← Set.ncard_univ] at key
    rw [Set.eq_of_subset_of_ncard_le (Set.subset_univ B) key.ge]

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.eq_univ_of_card_lt := eq_univ_of_card_lt
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.eq_univ_of_card_lt :=
  _root_.AddMonoidAction.IsBlock.eq_univ_of_card_lt

/-- If a block has too many translates, then it is a (sub)singleton -/
@[to_additive /-- If a block has too many translates, then it is a (sub)singleton -/]
theorem subsingleton_of_card_lt [Finite X] (hB : IsBlock G B)
    (hB' : Nat.card X < 2 * Set.ncard (orbit G B)) :
    B.Subsingleton := by
  suffices Set.ncard B < 2 by simp_all
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; simp
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h, lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb ↦ hB' (Nat.mul_le_mul_right _ hb)

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsBlock.subsingleton_of_card_lt := subsingleton_of_card_lt
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.subsingleton_of_card_lt :=
  _root_.AddMonoidAction.IsBlock.subsingleton_of_card_lt

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
  have hag : ∀ g : G, a ∈ g • B' → B' ≤ g • B' := by
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

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.IsBlock.of_subset := of_subset
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsBlock.of_subset := _root_.AddMonoidAction.IsBlock.of_subset

end IsBlock

end Finite

end Group

end MonoidAction
