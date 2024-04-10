/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir

-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Setoid.Partition
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Pointwise
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Subgroup.Actions

/-! # Blocks

Given `SMul G X`, an action of a type `G` on a type `X`, we define

- the predicate `MulAction.IsBlock G B` states that `B : Set X` is a block,
which means that the sets `g • B`, for `g ∈ G`, are pairwise disjoint.
Under `Group G` and `MulAction G X`, this is equivalent to the classical
definition `MulAction.IsBlock.def_one`

- a bunch of lemmas that give examples of “trivial” blocks : ⊥, ⊤, singletons,
and non trivial blocks: orbit of the group, orbit of a normal subgroup…

The non-existence of nontrivial blocks is the definition of primitive actions.

## Results for actions on finite sets

- `IsBlock.ncard_block_mul_ncard_orbit_eq` : The cardinality of a block
multiplied by the number of its translates is the cardinal of the ambient type

- `IsBlock.is_top_of_large_block` : a too large block is equal to top

- `IsBlock.is_subsingleton` : a too small block is a subsingleton

- `IsBlock.of_subset` : the intersections of the translates of a finite subset
that contain a given point is a block

## References

We follow [wielandt1964].

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
  · intro hB g g'
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
      simp only [Set.inf_eq_inter, Set.mem_inter_iff,
        ← Set.mem_smul_set_iff_inv_smul_mem, ← smul_smul, smul_inv_smul]
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
  intro g
  left
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
    {φ : G → H} (j : X →ₑ[φ] Y)
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
theorem IsBlock.smul {B : Set X} (g : G) (hB : IsBlock G B) :
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
  rintro B' ⟨g, rfl⟩; exact hB.smul g

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

section Stabilizer

/- For transitive actions, construction of the lattice equivalence
  `block_stabilizerOrderIso` between
  - blocks of `MulAction G X` containing a point `a ∈ X`,
  and
  - subgroups of G containing `stabilizer G a`.
  (Wielandt, th. 7.5) -/

/-- The orbit of a under a subgroup containing the stabilizer of a
 is a block -/
theorem IsBlock.of_orbit' {H : Subgroup G} {a : X} (hH : stabilizer G a ≤ H) :
    IsBlock G (MulAction.orbit H a) := by
  rw [IsBlock.mk_subset]; intro g b
  rintro ⟨h, rfl⟩
  simp only [Set.le_eq_subset]
  intro hb'
  suffices g ∈ H by
    rw [← Subgroup.coe_mk H g this, ← Subgroup.smul_def]
    apply smul_orbit_subset
  rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, ← MulAction.mul_smul] at hb'
  obtain ⟨k : ↥H, hk⟩ := hb'
  simp only at hk
  rw [MulAction.mul_smul, ← smul_eq_iff_eq_inv_smul, ← inv_inv (h : G), ← smul_eq_iff_eq_inv_smul, ←
    MulAction.mul_smul, Subgroup.smul_def, ← MulAction.mul_smul] at hk
  rw [← mem_stabilizer_iff] at hk
  let hk' := hH hk
  rw [Subgroup.mul_mem_cancel_right, Subgroup.mul_mem_cancel_left] at hk'
  exact hk'
  apply Subgroup.inv_mem; exact SetLike.coe_mem h
  exact SetLike.coe_mem k

/-- If B is a block containing a , then the stabilizer of B contains the stabilizer of a -/
theorem IsBlock.stabilizer_le
    {B : Set X} (hB : IsBlock G B) {a : X} (ha : a ∈ B) :
    stabilizer G a ≤ stabilizer G B := by
  intro g hg
  rw [mem_stabilizer_iff] at hg ⊢
  cases' IsBlock.def_one.mp hB g with h h'
  exact h
  exfalso; rw [← Set.mem_empty_iff_false a]
  simp only [disjoint_iff, Set.inf_eq_inter, Set.bot_eq_empty] at h'
  rw [← h', Set.mem_inter_iff]
  constructor
  rw [← hg]; rw [Set.smul_mem_smul_set_iff]; exact ha
  exact ha

/-- A block is the orbit of a under its stabilizer -/
theorem IsBlock.orbit_stabilizer_eq
    [htGX : IsPretransitive G X] {B : Set X} (hB : IsBlock G B)
    {a : X} (ha : a ∈ B) : MulAction.orbit (stabilizer G B) a = B := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    let z := mem_stabilizer_iff.mp (SetLike.coe_mem k)
    rw [← Subgroup.smul_def] at z
    let zk : k • a ∈ k • B := Set.smul_mem_smul_set_iff.mpr ha
    rw [z] at zk; exact zk
  · intro hx
    obtain ⟨k, rfl⟩ := exists_smul_eq G a x
    suffices k ∈ stabilizer G B by
      exact ⟨⟨k, this⟩, rfl⟩
    rw [mem_stabilizer_iff]
    exact IsBlock.def_mem hB ha hx

/-- A subgroup containing the stabilizer of `a`
  is the stabilizer of the orbit of `a` under that subgroup -/
theorem stabilizer_orbit_eq {a : X} {H : Subgroup G}
    (hH : stabilizer G a ≤ H) :
    stabilizer G (orbit H a) = H := by
  ext g; constructor
  · intro hg; rw [mem_stabilizer_iff] at hg
    suffices g • a ∈ orbit H a by
      rw [mem_orbit_iff] at this
      obtain ⟨k, hk⟩ := this
      rw [← Subgroup.mul_mem_cancel_left H (SetLike.coe_mem k⁻¹)]
      rw [smul_eq_iff_eq_inv_smul] at hk
      apply hH
      rw [mem_stabilizer_iff]; rw [MulAction.mul_smul]
      rw [← Subgroup.smul_def]; exact hk.symm
    rw [← hg]
    simp only [Set.smul_mem_smul_set_iff, mem_orbit_self]
  intro hg
  rw [mem_stabilizer_iff]
  rw [← Subgroup.coe_mk H g hg, ← Subgroup.smul_def]
  apply smul_orbit

variable (G)

/-- Order equivalence between blocks in X containing a point a
 and subgroups of G containing the stabilizer of a (Wielandt, th. 7.5)-/
def block_stabilizerOrderIso [htGX : IsPretransitive G X] (a : X) :
    { B : Set X // a ∈ B ∧ IsBlock G B } ≃o Set.Ici (stabilizer G a) where
  toFun := fun ⟨B, ha, hB⟩ => ⟨stabilizer G B, hB.stabilizer_le ha⟩
  invFun := fun ⟨H, hH⟩ =>
    ⟨MulAction.orbit H a, MulAction.mem_orbit_self a, IsBlock.of_orbit' hH⟩
  left_inv := fun ⟨B, ha, hB⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (hB.orbit_stabilizer_eq ha)
  right_inv := fun ⟨H, hH⟩ =>
    (id (propext Subtype.mk_eq_mk)).mpr (stabilizer_orbit_eq hH)
  map_rel_iff' := by
    rintro ⟨B, ha, hB⟩; rintro ⟨B', ha', hB'⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Set.le_eq_subset]
    constructor
    · rintro hBB' b hb
      obtain ⟨k, rfl⟩ := htGX.exists_smul_eq a b
      suffices k ∈ stabilizer G B by
        apply hBB' at this
        simp only [mem_stabilizer_iff] at this
        rw [← this, Set.smul_mem_smul_set_iff]
        exact ha'
      simp only [mem_stabilizer_iff]
      exact hB.def_mem ha hb
    · intro hBB'
      intro g
      simp only [mem_stabilizer_iff]
      intro hgB
      apply IsBlock.def_mem hB' ha'
      apply hBB'
      rw [← hgB]
      simp_rw [Set.smul_mem_smul_set_iff]; exact ha

end Stabilizer

section Fintype

theorem Setoid.nat_sum {α : Type _} [Finite α] {c : Set (Set α)} (hc : Setoid.IsPartition c) :
    (finsum fun x : c => Set.ncard (x : Set α)) = Nat.card α := by
  classical
  have := Fintype.ofFinite α
  simp only [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← Set.Nat.card_coe_set_eq]
  rw [← Fintype.card_sigma]
  refine' Fintype.card_congr (Equiv.ofBijective (fun x => x.snd : (Σ a : ↥c, a) → α) _)
  constructor
  -- injectivity
  rintro ⟨⟨x, hx⟩, ⟨a, ha : a ∈ x⟩⟩ ⟨⟨y, hy⟩, ⟨b, hb : b ∈ y⟩⟩ hab
  dsimp at hab
  rw [hab] at ha
  rw [Sigma.subtype_ext_iff]
  simp only [Subtype.mk_eq_mk, Subtype.coe_mk]
  apply And.intro _ hab
  refine' ExistsUnique.unique (hc.2 b) _ _
  simp only [exists_unique_iff_exists, exists_prop]
  exact ⟨hx, ha⟩
  simp only [exists_unique_iff_exists, exists_prop]
  exact ⟨hy, hb⟩
  -- surjectivity
  intro a
  obtain ⟨x, ⟨hx, ha : a ∈ x, _⟩, _⟩ := hc.2 a
  use ⟨⟨x, hx⟩, ⟨a, ha⟩⟩

theorem Set.ncard_coe {α : Type*} (s : Set α) :
    s.ncard = Set.ncard (Set.univ : Set (Set.Elem s)) := by
  apply Set.ncard_congr (fun a ha ↦ ⟨a, ha⟩)
  · exact fun a ha ↦ by simp only [Set.mem_univ]
  · simp [Subtype.mk_eq_mk]
  · exact fun ⟨a, ha⟩ _ ↦ ⟨a, ha, rfl⟩

/-- The cardinality of the ambient is the product of
  of the cardinality of a block
  by the cardinality of the set of translates of that block -/
theorem IsBlock.ncard_block_mul_ncard_orbit_eq
    [Finite X] [IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B * Set.ncard (Set.range fun g : G => g • B) = Nat.card X := by
  classical
  have := Fintype.ofFinite X
  rw [← Setoid.nat_sum (hB.isBlockSystem hB_ne).1]
  simp only [finsum_eq_sum_of_fintype]
  rw [Finset.sum_congr rfl]
  · rw [Finset.sum_const, mul_comm]
    congr
    rw [← Set.ncard_coe_Finset, Finset.coe_univ, Set.ncard_coe]
  · rintro ⟨x, ⟨g, rfl⟩⟩ _
    exact Set.ncard_image_of_injective B (MulAction.injective g)

/-- The cardinality of a block divides the cardinality of the ambient type -/
theorem IsBlock.ncard_of_block_divides [Finite X] [IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hB_ne : B.Nonempty) :
    Set.ncard B ∣ Nat.card X :=
  Dvd.intro _ (hB.ncard_block_mul_ncard_orbit_eq hB_ne)

/-- A too large block is equal to ⊤ -/
theorem IsBlock.is_top_of_large_block [hfX : Finite X] [hGX : IsPretransitive G X] {B : Set X}
    (hB : IsBlock G B) (hB' : Nat.card X < Set.ncard B * 2) : B = ⊤ := by
  classical
  letI := Fintype.ofFinite X
  cases' Set.eq_empty_or_nonempty B with hB_e hB_ne
  -- case when B is empty (exfalso)
  · exfalso; rw [hB_e] at hB'
    simp only [Set.ncard_empty, zero_mul, gt_iff_lt, not_lt_zero'] at hB'
  -- case when B is not empty
  rw [Set.top_eq_univ, ← Set.toFinset_inj, Set.toFinset_univ,
    ← Finset.card_eq_iff_eq_univ, ← Set.ncard_eq_toFinset_card',
    ← Nat.card_eq_fintype_card]
  obtain ⟨k, h⟩ := hB.ncard_of_block_divides hB_ne
  suffices k = 1 by
    simp only [h, this, mul_one]
  rw [h, Nat.mul_lt_mul_left ?_] at hB'
  apply Nat.eq_of_le_of_lt_succ ?_ hB'
  apply Nat.pos_of_ne_zero
  intro hk
  rw [hk, mul_zero] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff] at h
  exact hB_ne.ne_empty B.eq_empty_of_isEmpty
  rwa [← Set.ncard_pos] at hB_ne

/-- If a block has too many translates, then it is a (sub)singleton  -/
theorem IsBlock.is_subsingleton [Finite X] [IsPretransitive G X]
    {B : Set X} (hB : IsBlock G B)
    (hB' : Nat.card X < 2 * Set.ncard (Set.range fun g : G => (g • B : Set X))) :
    B.Subsingleton := by
  suffices Set.ncard B < 2 by
    rw [Nat.lt_succ_iff, Set.ncard_le_one_iff_eq] at this
    cases this with
    | inl h => rw [h]; exact Set.subsingleton_empty
    | inr h =>
      obtain ⟨a, ha⟩ := h; rw [ha]; exact Set.subsingleton_singleton
  cases Set.eq_empty_or_nonempty B with
  | inl h => rw [h, Set.ncard_empty]; norm_num
  | inr h =>
    rw [← hB.ncard_block_mul_ncard_orbit_eq h, lt_iff_not_ge] at hB'
    rw [← not_le]
    exact fun hb ↦ hB' (Nat.mul_le_mul_right _ hb)

-- TODO : Is the assumption B.finite necessary ?
/-- The intersection of the translates of a *finite* subset which contain a given point
is a block (Wielandt, th. 7.3 )-/
theorem IsBlock.of_subset [IsPretransitive G X] (a : X) (B : Set X) (hfB : B.Finite) :
    IsBlock G (⋂ (k : G) (_ : a ∈ k • B), k • B) := by
  let B' := ⋂ (k : G) (_ : a ∈ k • B), k • B
  cases' Set.eq_empty_or_nonempty B with hfB_e hfB_ne
  · suffices (⋂ (k : G) (_ : a ∈ k • B), k • B) = Set.univ by
      rw [this]; apply top_IsBlock
    simp only [Set.iInter_eq_univ]
    intro k hk; exfalso
    rw [hfB_e] at hk; simpa only [Set.smul_set_empty] using hk

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
    use g⁻¹ • x
    constructor
    · apply Set.mem_biInter; intro k; rintro (hk : a ∈ k • B)
      rw [← Set.mem_smul_set_iff_inv_smul_mem, smul_smul]
      apply hB'₀
      rw [← smul_smul, Set.mem_smul_set_iff_inv_smul_mem]
      apply hB'₀ k hk
      rw [← Set.mem_smul_set_iff_inv_smul_mem]
      exact hg
      exact hx
    · simp only [smul_inv_smul]
  have hag' : ∀ g : G, a ∈ g • B' → B' = g • B' := by
    intro g hg
    apply symm
    rw [← mem_stabilizer_iff]
    rw [← Subgroup.inv_mem_iff (stabilizer G B')]
    rw [mem_stabilizer_of_finite_iff_smul_le B' hfB' g⁻¹]
    simp_rw [← Set.subset_set_smul_iff]
    exact hag g hg
  rw [IsBlock.mk_notempty_one]
  intro g hg
  rw [← Set.nonempty_iff_ne_empty] at hg
  obtain ⟨b : X, hb' : b ∈ g • B', hb : b ∈ B'⟩ := Set.nonempty_def.mp hg
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

end Fintype


end Group

end MulAction
