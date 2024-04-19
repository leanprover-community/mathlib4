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
  which means that the sets `g • B`, for `g ∈ G`, are equal or disjoint.

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

theorem orbit.eq_or_disjoint (a b : X) :
    orbit G a = orbit G b ∨ Disjoint (orbit G a) (orbit G b) := by
  apply (em (Disjoint (orbit G a) (orbit G b))).symm.imp _ id
  simp (config := { contextual := true })
    only [Set.not_disjoint_iff, ← orbit_eq_iff, forall_exists_index, and_imp, eq_comm, implies_true]

theorem orbit.pairwiseDisjoint :
    (Set.range fun x : X => orbit G x).PairwiseDisjoint id := by
  rintro s ⟨x, rfl⟩ t ⟨y, rfl⟩ h
  contrapose! h
  exact (orbit.eq_or_disjoint x y).resolve_right h

/- -- move this to `Mathlib.Data.Setoid.Partition`
lemma _root_.Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty {α : Type*} {s : Set (Set α)}
    (h₁ : s.PairwiseDisjoint id) (h₂ : ∀ a : α, ∃ x ∈ s, a ∈ x) (h₃ : ∅ ∉ s) :
    Setoid.IsPartition s := by
  refine ⟨h₃, fun a ↦ ?_⟩
  simp only [exists_unique_iff_exists, exists_prop]
  apply exists_unique_of_exists_of_unique (h₂ a)
  intro b₁ b₂ hb₁ hb₂
  apply h₁.elim hb₁.1 hb₂.1
  simp only [Set.not_disjoint_iff]
  exact ⟨a, hb₁.2, hb₂.2⟩
-/

/- moved to Mathlib.Data.Set.Pairwise.Basic
-- move this to one of
-- [Mathlib.Order.Atoms, Mathlib.Data.Finset.Lattice, Mathlib.Order.CompleteLatticeIntervals]
lemma _root_.Set.PairwiseDisjoint.eq_or_disjoint {α : Type*} {s : Set (Set α)}
    (h : s.PairwiseDisjoint id) {a b : Set α} (ha : a ∈ s) (hb : b ∈ s) :
    a = b ∨ Disjoint a b := by
  rw [or_iff_not_imp_right]
  exact h.elim ha hb
-/

/-
moved to
-- move this to one of
-- [Mathlib.Order.Atoms, Mathlib.Data.Finset.Lattice, Mathlib.Order.CompleteLatticeIntervals]
lemma _root_.Set.pairwiseDisjoint_range_iff {α β : Type*} {f : α → (Set β)} :
    (Set.range f).PairwiseDisjoint id ↔ ∀ x y, f x = f y ∨ Disjoint (f x) (f y) := by
  constructor
  · intro h x y
    apply h.eq_or_disjoint (Set.mem_range_self x) (Set.mem_range_self y)
  · rintro h _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact (h x y).resolve_left hxy
-/

/-- Orbits of an element form a partition -/
theorem IsPartition.of_orbits :
    Setoid.IsPartition (Set.range fun a : X => orbit G a) := by
  apply orbit.pairwiseDisjoint.isPartition_of_exists_of_ne_empty
  · intro x
    exact ⟨_, ⟨x, rfl⟩, mem_orbit_self x⟩
  · rintro ⟨a, ha : orbit G a = ∅⟩
    exact (MulAction.orbit_nonempty a).ne_empty ha

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
  apply Set.pairwiseDisjoint_range_iff

/-- Alternate definition of a block -/
theorem IsBlock.mk_notempty {B : Set X} :
    IsBlock G B ↔ ∀ g g' : G, g • B ∩ g' • B ≠ ∅ → g • B = g' • B := by
  simp_rw [IsBlock.def, or_iff_not_imp_right, Set.disjoint_iff_inter_eq_empty]

/-- A fixed block is a block -/
theorem IsFixedBlock.isBlock {B : Set X} (hfB : IsFixedBlock G B) :
    IsBlock G B := by
  simp [IsBlock.def, hfB _]

variable (X)

/-- The empty set is a block -/
theorem isBlock_empty : IsBlock G (⊥ : Set X) := by
  simp [IsBlock.def, Set.bot_eq_empty, Set.smul_set_empty]

variable {X}

theorem isBlock_singleton (a : X) : IsBlock G ({a} : Set X) := by
  simp [IsBlock.def, Classical.or_iff_not_imp_left]

/-- Subsingletons are (trivial) blocks -/
theorem isBlock_subsingleton {B : Set X} (hB : B.Subsingleton) :
    IsBlock G B :=
  hB.induction_on (isBlock_empty _) isBlock_singleton

end SMul

section Group

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

theorem IsBlock.def_one {B : Set X} :
    IsBlock G B ↔ ∀ g : G, g • B = B ∨ Disjoint (g • B) B := by
  rw [IsBlock.def]; constructor
  · intro hB g
    simpa only [one_smul] using hB g 1
  · intro hB g g'
    apply (hB (g'⁻¹ * g)).imp
    · rw [← smul_smul, ← eq_inv_smul_iff, inv_inv]
      exact id
    · intro h
      rw [Set.disjoint_iff] at h ⊢
      rintro x hx
      suffices g'⁻¹ • x ∈ (g'⁻¹ * g) • B ∩ B by apply h this
      simp only [Set.mem_inter_iff, ← Set.mem_smul_set_iff_inv_smul_mem, ← smul_smul, smul_inv_smul]
      exact hx

theorem IsBlock.mk_notempty_one {B : Set X} :
    IsBlock G B ↔ ∀ g : G, g • B ∩ B ≠ ∅ → g • B = B := by
  simp_rw [IsBlock.def_one, Set.disjoint_iff_inter_eq_empty, or_iff_not_imp_right]

theorem IsBlock.mk_mem {B : Set X} :
    IsBlock G B ↔ ∀ (g : G) (a : X) (_ : a ∈ B) (_ : g • a ∈ B), g • B = B := by
  rw [IsBlock.mk_notempty_one]
  simp only [← Set.nonempty_iff_ne_empty, Set.nonempty_def, Set.mem_inter_iff,
    exists_imp, and_imp, Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro H g a ha hga
    apply H g (g • a) _ hga
    simpa only [inv_smul_smul] using ha
  · intro H g a ha hga
    rw [← eq_inv_smul_iff, eq_comm]
    exact H g⁻¹ a hga ha

theorem IsBlock.def_mem {B : Set X} (hB : IsBlock G B) {a : X} {g : G} :
    a ∈ B → g • a ∈ B → g • B = B :=
  IsBlock.mk_mem.mp hB g a

theorem IsBlock.mk_subset {B : Set X} :
    IsBlock G B ↔ ∀ {g : G} {b : X} (_ : b ∈ B) (_ : b ∈ g • B), g • B ≤ B := by
  simp_rw [IsBlock.mk_notempty_one, ← Set.nonempty_iff_ne_empty]
  constructor
  · intro hB g b hb hgb
    exact (hB g ⟨b, hgb, hb⟩).le
  · intro hB g ⟨b, hb', hb⟩
    apply le_antisymm (hB hb hb')
    suffices g⁻¹ • B ≤ B by
      rw [Set.le_iff_subset] at this ⊢
      rwa [← inv_inv g, ← Set.set_smul_subset_iff]
    exact hB (Set.mem_smul_set_iff_inv_smul_mem.mp hb') (Set.smul_mem_smul_set_iff.mpr hb)

/-- An invariant block is a fixed block -/
theorem IsInvariantBlock.isFixedBlock {B : Set X} (hfB : IsInvariantBlock G B) :
    IsFixedBlock G B := by
  intro g
  apply le_antisymm (hfB g)
  intro x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  apply hfB g⁻¹
  rwa [Set.smul_mem_smul_set_iff]

/-- An invariant block is a block -/
theorem IsInvariantBlock.isBlock {B : Set X} (hfB : IsInvariantBlock G B) :
    IsBlock G B :=
  hfB.isFixedBlock.isBlock

/-- An orbit is a block -/
theorem isFixedBlock_orbit (a : X) : IsFixedBlock G (orbit G a) :=
  (smul_orbit · a)

/-- An orbit is a block -/
theorem isBlock_orbit (a : X) : IsBlock G (orbit G a) :=
  (isFixedBlock_orbit a).isBlock

variable (X)

/-- The full set is a (trivial) block -/
theorem isFixedBlock_top : IsFixedBlock G (⊤ : Set X) :=
  fun _ ↦ by simp only [Set.top_eq_univ, Set.smul_set_univ]

/-- The full set is a (trivial) block -/
theorem isBlock_top : IsBlock G (⊤ : Set X) :=
  (isFixedBlock_top _).isBlock

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
  apply (IsBlock.def_one.mp hB (φ g)).imp
  · intro heq
    rw [← Group.preimage_smul_setₛₗ Y X φ j, heq]
  · rw [← Group.preimage_smul_setₛₗ Y X φ j]
    exact Disjoint.preimage _

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
      exact IsBlock.def_one.mp (isBlock_top X)
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
theorem orbit.isBlock_of_normal' {N : Subgroup G} (nN : Subgroup.Normal N) (a : X) :
    IsBlock G (orbit N a) := by
  unfold IsBlock
  convert Set.Pairwise.mono _ (orbit.pairwiseDisjoint (G := N))
  rintro _ ⟨g, rfl⟩
  suffices g • (orbit N a) = orbit N (g • a) by
    simp only [this, Set.mem_range, exists_apply_eq_apply]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · rintro ⟨k, hk⟩
    rw [← smul_eq_iff_eq_inv_smul] at hk
    use ⟨g * k * g⁻¹, nN.conj_mem k k.prop g⟩
    simp only [Submonoid.mk_smul, ← smul_smul, ← hk, inv_smul_smul]
    rfl
  · rintro ⟨k, rfl⟩
    simp only
    use ⟨g⁻¹ * k * g, by
      convert nN.conj_mem k k.prop g⁻¹
      simp only [inv_inv]⟩
    simp only [Submonoid.mk_smul, ← smul_smul]
    rfl
  exact N.toSubmonoid.mulAction

/-- An orbit of a normal subgroup is a block -/
theorem orbit.isBlock_of_normal {N : Subgroup G} (nN : Subgroup.Normal N) (a : X) :
    IsBlock G (orbit N a) := by
  rw [IsBlock.def_one]
  intro g
  suffices g • orbit N a = orbit N (g • a) by rw [this]; apply orbit.eq_or_disjoint
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
