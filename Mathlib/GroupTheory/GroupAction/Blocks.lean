/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Setoid.Partition
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Pointwise
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Subgroup.Actions

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `IsBlock G B` states that `B : Set X` is a block,
  which means that the sets `g • B`, for `g ∈ G` form a partition of `X`.

- a bunch of lemmas that give examples of “trivial” blocks : ⊥, ⊤, singletons,
  and non trivial blocks: orbit of the group, orbit of a normal subgroup…

The non-existence of nontrivial blocks is the definition of primitive actions.

## References

We follow [wieland1964].

-/

open scoped BigOperators Pointwise

namespace MulAction

section orbits

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

theorem orbit.equal_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) := by
  cases' em (Disjoint (orbit G a) (orbit G b)) with h h
  · apply Or.intro_right; exact h
  apply Or.intro_left
  rw [Set.not_disjoint_iff] at h
  obtain ⟨x, hxa, hxb⟩ := h
  rw [← orbit_eq_iff] at hxa hxb
  rw [← hxa, ← hxb]

-- TODO : simplify using the preceding orbit.eq_or_disjoint?
/-- Orbits of an element form a partition -/
theorem IsPartition.of_orbits :
    Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  constructor
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact Set.Nonempty.ne_empty (MulAction.orbit_nonempty a) ha
  intro a; use orbit G a
  constructor
  · simp only [Set.mem_range_self, mem_orbit_self, exists_unique_iff_exists, exists_true_left]
  · simp only [Set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff']
    rintro B b ⟨rfl⟩ ha
    apply symm
    rw [orbit_eq_iff]
    exact ha

end orbits

section SMul

variable (G : Type*) {X : Type*} [SMul G X]

-- Change terminology : is_fully_invariant ?
/-- A fixed block is a fully invariant subset -/
def IsFixedBlock (B : Set X) := ∀ g : G, g • B = B

/-- An invariant block is a set which is stable under has_smul -/
def IsInvariantBlock (B : Set X) := ∀ g : G, g • B ≤ B

/-- A trivial block is a subsingleton or ⊤ (it is not necessarily a block…)-/
def IsTrivialBlock (B : Set X) := B.Subsingleton ∨ B = ⊤

/-- A block is a set whose translates are pairwise disjoint -/
def IsBlock (B : Set X) := (Set.range fun g : G => g • B).PairwiseDisjoint id

variable {G}

/-- A set B is a block iff for all g, g',
the sets g • B and g' • B are either equal or disjoint -/
theorem IsBlock.def {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B = g' • B ∨ Disjoint (g • B) (g' • B) := by
  constructor
  · intro hB g g'
    by_cases h : g • B = g' • B
    · left; exact h
    · right; exact hB (Set.mem_range_self g) (Set.mem_range_self g') h
  · intro hB
    rintro C ⟨g, rfl⟩ C' ⟨g', rfl⟩ hgg'
    cases hB g g' with
    | inl h => exfalso; exact hgg' h
    | inr h => exact h

/-- Alternate definition of a block -/
theorem IsBlock.mk_notempty {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B ∩ g' • B ≠ ∅ → g • B = g' • B := by
  rw [IsBlock.def]
  apply forall_congr'; intro g
  apply forall_congr'; intro g'
  rw [Set.disjoint_iff_inter_eq_empty]
  exact or_iff_not_imp_right

/-- A fixed block is a block -/
theorem IsFixedBlock.isBlock {B : Set X} (hfB : IsFixedBlock G B) :
    IsBlock G B := by
  rw [IsBlock.def]
  intro g g'
  apply Or.intro_left
  rw [hfB g, hfB g']

variable (X)

/-- The empty set is a block -/
theorem isBlock_empty : IsBlock G (⊥ : Set X) := by
  rw [IsBlock.def]
  intro g g'; apply Or.intro_left
  simp only [Set.bot_eq_empty, Set.smul_set_empty]

variable {X}

theorem isBlock_singleton (a : X) : IsBlock G ({a} : Set X) := by
  rw [IsBlock.def]
  intro g g'
  simp [Classical.or_iff_not_imp_left]

/-- Subsingletons are (trivial) blocks -/
theorem isBlock_subsingleton {B : Set X} (hB : B.Subsingleton) :
    IsBlock G B := by cases Set.Subsingleton.eq_empty_or_singleton hB with
  | inl h => rw [h]; apply isBlock_empty
  | inr h => obtain ⟨a, rfl⟩ := h; apply isBlock_singleton

end SMul

section Group

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

theorem IsBlock.def_one {B : Set X} :
    IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B := by
  rw [IsBlock.def]; constructor
  · intro hB g
    simpa only [one_smul] using hB g 1
  · intro hB
    intro g g'
    cases hB (g'⁻¹ * g) with
    | inl h =>
      apply Or.intro_left
      rw [← inv_inv g', eq_inv_smul_iff, smul_smul]
      exact h
    | inr h =>
      apply Or.intro_right
      rw [Set.disjoint_iff] at h ⊢
      rintro x ⟨hx, hx'⟩
      simp only [Set.mem_empty_iff_false]
      suffices g'⁻¹ • x ∈ (g'⁻¹ * g) • B ⊓ B by
        apply h this
      simp only [Set.inf_eq_inter, Set.mem_inter_iff]
      simp only [← Set.mem_smul_set_iff_inv_smul_mem]
      rw [← smul_smul]; rw [smul_inv_smul]
      exact ⟨hx, hx'⟩

theorem IsBlock.mk_notempty_one {B : Set X} :
    IsBlock G B ↔ ∀ g : G, g • B ∩ B ≠ ∅ → g • B = B := by
  rw [IsBlock.def_one]
  apply forall_congr'
  intro g
  rw [Set.disjoint_iff_inter_eq_empty]
  exact or_iff_not_imp_right

theorem IsBlock.mk_mem {B : Set X} :
    IsBlock G B ↔
      ∀ (g : G) (a : X) (_ : a ∈ B) (_ : g • a ∈ B), g • B = B := by
  rw [IsBlock.mk_notempty_one]
  simp only [← Set.nonempty_iff_ne_empty, Set.nonempty_def, Set.mem_inter_iff,
    exists_imp, and_imp, Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro H g a ha hga
    apply H g (g • a) _ hga
    simp only [inv_smul_smul]; exact ha
  · intro H g a ha hga
    rw [← eq_inv_smul_iff, eq_comm]
    exact H g⁻¹ a hga ha

theorem IsBlock.def_mem {B : Set X} (hB : IsBlock G B) {a : X} {g : G} :
    a ∈ B → g • a ∈ B → g • B = B :=
  IsBlock.mk_mem.mp hB g a

theorem IsBlock.mk_subset {B : Set X} :
    IsBlock G B ↔ ∀ {g : G} {b : X} (_ : b ∈ B) (_ : b ∈ g • B), g • B ≤ B := by
  constructor
  · intro hB g b hb hgb
    rw [Set.le_iff_subset, Set.set_smul_subset_iff,
      hB.def_mem hb (Set.mem_smul_set_iff_inv_smul_mem.mp hgb)]
  · rw [IsBlock.mk_notempty_one]
    intro hB g hg
    rw [← Set.nonempty_iff_ne_empty] at hg
    obtain ⟨b : X, hb' : b ∈ g • B, hb : b ∈ B⟩ := Set.nonempty_def.mp hg
    apply le_antisymm
    · exact hB hb hb'
    suffices g⁻¹ • B ≤ B by
      rw [Set.le_iff_subset] at this ⊢
      rw [← inv_inv g, ← Set.set_smul_subset_iff]; exact this
    exact hB (Set.mem_smul_set_iff_inv_smul_mem.mp hb')
      (Set.smul_mem_smul_set_iff.mpr hb)

/-- An invariant block is a block -/
theorem IsInvariantBlock.isBlock {B : Set X} (hfB : IsInvariantBlock G B) :
    IsBlock G B := by
  rw [IsBlock.def_one]
  intro g; apply Or.intro_left
  apply le_antisymm
  exact hfB g
  · intro x hx
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    apply hfB g⁻¹
    rw [Set.smul_mem_smul_set_iff]; exact hx

/-- An orbit is a block -/
theorem IsBlock_of_orbit (a : X) : IsBlock G (orbit G a) := by
  apply IsFixedBlock.isBlock
  intro g; apply smul_orbit

variable (X)

/-- The full set is a (trivial) block -/
theorem top_IsBlock : IsBlock G (⊤ : Set X) := by
  apply IsFixedBlock.isBlock
  intro g
  simp only [Set.top_eq_univ, Set.smul_set_univ]

variable {X}

/-- Is B is a block for an action G, it is a block for the action of any subgroup of G -/
theorem IsBlock.subgroup {H : Subgroup G} {B : Set X} (hfB : IsBlock G B) :
    IsBlock H B := by
  rw [IsBlock.def_one]; rintro ⟨g, _⟩
  simpa only using IsBlock.def_one.mp hfB g

theorem IsBlock.preimage {H Y : Type*} [Group H] [MulAction H Y]
    {φ : H → G} (j : Y →ₑ[φ] X) {B : Set X} (hB : IsBlock G B) :
    IsBlock H (j ⁻¹' B) := by
  rw [IsBlock.def_one]
  intro g
  cases' IsBlock.def_one.mp hB (φ g) with heq hdis
  · left
    rw [← Group.preimage_smul_setₛₗ Y X φ j, heq]
  · right
    rw [← Group.preimage_smul_setₛₗ Y X φ j]
    exact Disjoint.preimage _ hdis

theorem IsBlock.image {H Y : Type*} [Group H] [MulAction H Y]
    {φ : G →* H} (j : X →ₑ[φ] Y)
    (hφ : Function.Surjective φ) (hj : Function.Injective j)
    {B : Set X} (hB : IsBlock G B) :
    IsBlock H (j '' B) := by
  rw [IsBlock.def]
  intro h h'
  obtain ⟨g, rfl⟩ := hφ h
  obtain ⟨g', rfl⟩ := hφ h'
  simp only [← image_smul_setₛₗ X Y φ j]
  cases' IsBlock.def.mp hB g g' with h h
  · left; rw [h]
  · right; exact Set.disjoint_image_of_injective hj h

theorem IsBlock.subtype_val_preimage {C : SubMulAction G X} {B : Set X} (hB : IsBlock G B) :
    IsBlock G (Subtype.val ⁻¹' B : Set C) :=
  hB.preimage C.inclusion

/-
theorem IsBlock.smul_coe_eq_coe_smul {C : SubMulAction G X} {B : Set C} {g : G} :
    g • (Subtype.val '' B : Set X) = Subtype.val '' (g • B) :=
  (image_smul_set G _ X C.inclusion g B).symm
-/

theorem IsBlock.iff_of_subtype_val {C : SubMulAction G X} {B : Set C} :
    IsBlock G B ↔ IsBlock G (Subtype.val '' B : Set X) := by
  simp only [IsBlock.def_one]
  apply forall_congr'
  intro g
  erw [← image_smul_set _ _ _ C.inclusion g B]
  apply or_congr (Set.image_eq_image Subtype.coe_injective).symm
  simp only [Set.disjoint_iff, Set.subset_empty_iff]
  erw [←
    Set.InjOn.image_inter (Set.injOn_of_injective Subtype.coe_injective _)
      (Set.subset_univ _) (Set.subset_univ _)]
  simp only [Set.image_eq_empty]

theorem IsBlock.iff_of_top (B : Set X) :
    IsBlock G B ↔ IsBlock (⊤ : Subgroup G) B := by
  simp only [IsBlock.def_one]
  constructor
  intro h g; exact h g
  intro h g; exact h ⟨g, Subgroup.mem_top g⟩

/-- The intersection of two blocks is a block -/
theorem IsBlock.inter {B₁ B₂ : Set X} (h₁ : IsBlock G B₁) (h₂ : IsBlock G B₂) :
    IsBlock G (B₁ ∩ B₂) := by
  rw [IsBlock.def_one]
  intro g
  rw [Set.smul_set_inter]
  cases' IsBlock.def_one.mp h₁ g with h₁ h₁
  · cases' IsBlock.def_one.mp h₂ g with h₂ h₂
    · apply Or.intro_left; rw [h₁, h₂]
    apply Or.intro_right
    apply Disjoint.inter_left'; apply Disjoint.inter_right'
    exact h₂
  · apply Or.intro_right
    apply Disjoint.inter_left; apply Disjoint.inter_right
    exact h₁

/-- An intersection of blocks is a block -/
theorem IsBlock.iInter {ι : Type*} {B : ι → Set X} (hB : ∀ i : ι, IsBlock G (B i)) :
    IsBlock G (⋂ i, B i) := by
  rw [IsBlock.def_one]
  cases' em (IsEmpty ι) with hι hι
  · -- ι = ∅, block = ⊤
    suffices (⋂ i : ι, B i) = Set.univ by
      rw [this]
      exact IsBlock.def_one.mp (top_IsBlock X)
    simp only [Set.top_eq_univ, Set.iInter_eq_univ]
    intro i; exfalso; apply hι.false; exact i
  intro g
  rw [Set.smul_set_iInter]
  cases' em (∃ i : ι, Disjoint (g • B i) (B i)) with h h
  · obtain ⟨j, hj⟩ := h
    apply Or.intro_right
    refine' Disjoint.mono _ _ hj
    apply Set.iInter_subset
    apply Set.iInter_subset
  simp only [not_exists] at h
  apply Or.intro_left
  have : ∀ i : ι, g • B i = B i := fun i => Or.resolve_right (IsBlock.def_one.mp (hB i) g) (h i)
  rw [Set.iInter_congr this]

theorem IsBlock.of_subgroup_of_conjugate {B : Set X} {H : Subgroup G} (hB : IsBlock H B) (g : G) :
    IsBlock (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) H) (g • B) := by
  rw [IsBlock.def_one]
  intro h'
  obtain ⟨h, hH, hh⟩ := Subgroup.mem_map.mp (SetLike.coe_mem h')
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hh
  suffices h' • g • B = g • h • B by
    simp only [this]
    cases' IsBlock.def_one.mp hB ⟨h, hH⟩ with heq hdis
    · left; congr
    · right
      exact Set.disjoint_image_of_injective (MulAction.injective g) hdis
  suffices (h' : G) • g • B = g • h • B by
    rw [← this]; rfl
  rw [← hh]
  rw [smul_smul (g * h * g⁻¹) g B]
  rw [smul_smul g h B]
  simp only [inv_mul_cancel_right]

/-- A translate of a block is a block -/
theorem IsBlock.translate {B : Set X} (g : G) (hB : IsBlock G B) :
    IsBlock G (g • B) := by
  rw [IsBlock.iff_of_top] at hB ⊢
  suffices Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) ⊤ = ⊤ by
    rw [← this]
    exact IsBlock.of_subgroup_of_conjugate hB g
  suffices ⊤ = Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj g)) ⊤ by
    rw [this]
    refine Subgroup.map_comap_eq_self_of_surjective ?_ _
    exact MulEquiv.surjective (MulAut.conj g)
  rw [Subgroup.comap_top]

variable (G)

/-- A block_system of X is a partition of X into blocks -/
def IsBlockSystem (B : Set (Set X)) :=
  Setoid.IsPartition B ∧ ∀ b : Set X, b ∈ B → IsBlock G b

variable {G}

-- The following proof is absurdly complicated !
/-- Translates of a block form a `block_system` -/
theorem IsBlock.isBlockSystem [hGX : MulAction.IsPretransitive G X]
    {B : Set X} (hB : IsBlock G B) (hBe : B.Nonempty) :
    IsBlockSystem G (Set.range fun g : G => g • B) := by
  constructor
  constructor
  · simp only [Set.mem_range, not_exists]
    intro x hx; apply Set.Nonempty.ne_empty hBe
    rw [← Set.image_eq_empty]
    exact hx
  · intro a
    obtain ⟨b : X, hb : b ∈ B⟩ := hBe
    obtain ⟨g, hab⟩ := exists_smul_eq G b a
    have hg : a ∈ g • B := by
      change a ∈ (fun b => g • b) '' B
      rw [Set.mem_image]
      use b
    use g • B
    constructor
    · simp only [Set.mem_range, exists_apply_eq_apply, exists_unique_iff_exists, exists_true_left]
      exact hg
    · simp only [Set.mem_range, exists_unique_iff_exists, exists_prop, and_imp, forall_exists_index,
        forall_apply_eq_imp_iff']
      intro B' g' hg' ha
      rw [← hg']
      apply symm
      apply Or.resolve_right (IsBlock.def.mp hB g g')
      rw [Set.not_disjoint_iff]
      use a
      rw [hg']
      exact ⟨hg, ha⟩
  rintro B' ⟨g, rfl⟩; exact hB.translate g

section Normal

/-- An orbit of a normal subgroup is a block -/
theorem orbit.isBlock_of_normal {N : Subgroup G} (nN : Subgroup.Normal N) (a : X) :
    IsBlock G (orbit N a) := by
  rw [IsBlock.def_one]
  intro g
  suffices g • orbit N a = orbit N (g • a) by rw [this]; apply orbit.equal_or_disjoint
  change ((fun x : X => g • x) '' Set.range fun k : N => k • a) = Set.range fun k : N => k • g • a
  simp only [Set.image_smul, Set.smul_set_range]
  ext
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    suffices g * k * g⁻¹ ∈ N by
      use ⟨g * k * g⁻¹, this⟩
      change (g * k * g⁻¹) • g • a = g • k • a
      rw [smul_smul, inv_mul_cancel_right, ← smul_smul]
    apply nN.conj_mem; exact hk
  · rintro ⟨⟨k, hk⟩, rfl⟩
    suffices g⁻¹ * k * g ∈ N by
      use ⟨g⁻¹ * k * g, this⟩
      change g • (g⁻¹ * k * g) • a = k • g • a
      simp only [← mul_assoc, ← smul_smul, smul_inv_smul, inv_inv]
    convert nN.conj_mem k hk g⁻¹
    rw [inv_inv]

/-- The orbits of a normal subgroup form a block system -/
theorem IsBlockSystem.of_normal {N : Subgroup G} (nN : Subgroup.Normal N) :
    IsBlockSystem G (Set.range fun a : X => orbit N a) := by
  constructor
  · apply IsPartition.of_orbits
  · intro b; rintro ⟨a, rfl⟩
    exact orbit.isBlock_of_normal nN a

end Normal

end Group

end MulAction
