/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.Reduce

import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Center and centralizers of free groups

This file develops the theory of commuting elements in a free group.

## Main statements

* `FreeGroup.center_eq_top_of_subsingleton` and `FreeGroup.center_eq_bot_of_nontrivial`: the center
  of a free group is `⊤` or `⊥`, depending on the number of generators.
* `IsFreeGroup.isCyclic_centralizer`: the centralizer of a non-unit element is a cyclic subgroup.
* `IsFreeGroup.commute_iff_exists_zpow`: two elements of a free group commute iff they are powers of
  the same element.

## Implementation

We show that, in a free group with at least two generators `a` and `b`, the center is trivial, by
showing directly in `FreeGroup.centralizer_of` that the elements that commute with `a` are exactly
its powers. It follows that the center of a free group is either everything (in the cyclic case) or
reduced to the identity. We deduce that the centralizer of a nontrivial element `v` is cyclic:
`centralizer {v}` is a free group which has a nontrivial center (as it contains `v`), so it is
cyclic.
-/

public section

namespace FreeGroup

open Subgroup

variable {α : Type*}

@[to_additive]
theorem mem_zpowers_of_iff [DecidableEq α] {a : α} {x : FreeGroup α} :
    x ∈ Subgroup.zpowers (of a) ↔ ∀ p ∈ x.toWord, p.1 = a := by
  refine ⟨by rintro ⟨_, rfl⟩; simp, fun h ↦ mk_toWord (x := x) ▸ ?_⟩
  generalize x.toWord = L at h
  induction L with
  | nil => exact one_mem _
  | cons p L ih =>
    rw [← List.singleton_append, ← mul_mk]
    refine mul_mem ?_ (ih (by grind))
    obtain ⟨b, _ | _⟩ := p
    all_goals
    · simp at h
      simp [h.1, mk_eq_of, mk_eq_inv_of]

@[to_additive]
theorem centralizer_of (a : α) : centralizer {of a} = zpowers (of a) := by
  classical
  refine le_antisymm ?_ (zpowers_le_centralizer_singleton _)
  refine fun x hx ↦ mem_zpowers_of_iff.mpr fun p hp ↦ ?_
  by_contra! hpne
  specialize hx (of a) rfl
  grind [idxOf_toWord_mul_of_eq x hpne hp, idxOf_toWord_of_mul_eq x hpne,
    List.idxOf_eq_zero_iff_eq_nil_or_head_eq]

@[to_additive]
theorem commute_of_iff {a : α} {x : FreeGroup α} :
    Commute (of a) x ↔ x ∈ zpowers (of a) := by
  rw [← centralizer_of, mem_centralizer_singleton_iff, Commute.symm_iff]

@[to_additive]
theorem center_eq_top_of_subsingleton [Subsingleton α] : center (FreeGroup α) = ⊤ :=
  center_eq_top

@[to_additive]
theorem center_eq_bot_of_nontrivial [Nontrivial α] : center (FreeGroup α) = ⊥ := by
  obtain ⟨a, b, hab⟩ := ‹_›
  refine eq_bot_iff_forall _ |>.mpr fun x hx ↦ ?_
  obtain ⟨n, hn⟩ := commute_of_iff.mp <| mem_center_iff.mp hx (of a)
  obtain ⟨m, rfl⟩ := commute_of_iff.mp <| mem_center_iff.mp hx (of b)
  simp [eq_of_of_zpow_eq_of_zpow hab hn]

end FreeGroup

namespace IsFreeGroup

open Subgroup

variable {G : Type*} [Group G] [IsFreeGroup G]

@[to_additive]
theorem isCyclic_iff_isMulCommutative : IsCyclic G ↔ IsMulCommutative G := by
  have e := IsFreeGroup.mulEquiv G
  rw [← e.isCyclic, ← e.isMulCommutative, FreeGroup.isCyclic_iff_subsingleton,
    FreeGroup.isMulCommutative_iff_subsingleton]

@[to_additive]
theorem center_eq_bot_or_top : center G = ⊥ ∨ center G = ⊤ := by
  have e := IsFreeGroup.mulEquiv G
  rw [← map_bot (e : FreeGroup (Generators G) →* G), ← map_equiv_top e, ← map_center_eq e,
    (map_injective e.injective).eq_iff, (map_injective e.injective).eq_iff]
  refine (subsingleton_or_nontrivial (Generators G)).symm.imp ?_ ?_
  · exact fun h ↦ FreeGroup.center_eq_bot_of_nontrivial
  · exact fun h ↦ FreeGroup.center_eq_top_of_subsingleton

@[to_additive]
theorem isCyclic_centralizer {g : G} (ha : g ≠ 1) : IsCyclic (centralizer {g}) := by
  rw [isCyclic_iff_isMulCommutative, ← center_eq_top_iff]
  apply center_eq_bot_or_top.resolve_left
  contrapose ha
  have : ⟨g, mem_centralizer_singleton_iff.mpr rfl⟩ ∈ center (centralizer {g}) := by
    simp [mem_center_iff, mem_centralizer_singleton_iff, commute_iff_eq]
  simpa [ha] using this

/-- Free groups are commutative-transitive. -/
@[to_additive /-- Free additive groups are commutative-transitive. -/]
theorem commute_trans {a b c : G} (h₁ : Commute a b) (h₂ : Commute b c) (hb : b ≠ 1) :
    Commute a c := by
  obtain ⟨g, hg⟩ := isCyclic_centralizer hb
  obtain ⟨n, hn⟩ := hg ⟨a, mem_centralizer_singleton_iff.mpr h₁.eq⟩
  obtain ⟨m, hm⟩ := hg ⟨c, mem_centralizer_singleton_iff.mpr h₂.symm.eq⟩
  simp [Subtype.ext_iff] at hn hm
  simp [← hn, ← hm]

@[to_additive]
theorem commute_iff_exists_zpow {a b : G} :
    Commute a b ↔ ∃ c, ∃ n m : ℤ, a = c ^ n ∧ b = c ^ m := by
  refine ⟨fun h ↦ ?_, by simp +contextual⟩
  by_cases hb : b = 1
  · exact ⟨a, 1, 0, by simp [hb]⟩
  obtain ⟨g, hg⟩ := isCyclic_centralizer hb
  obtain ⟨n, hn⟩ := hg ⟨a, mem_centralizer_singleton_iff.mpr h.eq⟩
  obtain ⟨m, hm⟩ := hg ⟨b, mem_centralizer_singleton_iff.mpr rfl⟩
  exact ⟨g, n, m, by simp_all [Subtype.ext_iff]⟩

end IsFreeGroup


namespace IsFreeGroup

variable {G : Type*} [Group G] [IsFreeGroup G] {u v w : G}

/-- A free group is commutative if and only if it is cyclic. -/
theorem isCyclic_iff_isMulCommutative : IsCyclic G ↔ IsMulCommutative G where
  mp h := h.isMulCommutative
  mpr h := by
    obtain ⟨ι, ⟨b⟩⟩ := IsFreeGroup.nonempty_basis (G := G)
    have hcomm : IsMulCommutative (FreeGroup ι) := b.repr.surjective.isMulCommutative
    have : IsCyclic (FreeGroup ι) := by
      rwa [FreeGroup.isCyclic_iff_subsingleton, ← FreeGroup.isMulCommutative_iff_subsingleton]
    exact (MulEquiv.isCyclic b.repr).mpr this

/-- In a free group, two elements commute iff they belong to a common cyclic subgroup. -/
theorem commute_iff_exists_mem_zpowers :
    Commute u v ↔ ∃ r : G, u ∈ Subgroup.zpowers r ∧ v ∈ Subgroup.zpowers r where
  mp h := by
    /- The key point: the subgroup generated by `u` and `v` is commutative and free (as a subgroup
    of a free group), so it is cyclic. -/
    set K : Subgroup G := Subgroup.closure ({u, v} : Set G)
    have hpair : ({u, v} : Set G).Pairwise Commute := Set.pairwise_pair_of_symm.mpr fun _ ↦ h
    have hK : IsCyclic K :=
      isCyclic_iff_isMulCommutative.mpr (Subgroup.isMulCommutative_closure hpair)
    obtain ⟨r, hr⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq K).mp hK
    exact ⟨r, by rw [hr]; exact Subgroup.subset_closure (by simp),
      by rw [hr]; exact Subgroup.subset_closure (by simp)⟩
  mpr h := by
    obtain ⟨r, hu, hw⟩ := h
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.refl r).zpow_zpow m n

/-- In a free group, two elements commuting with a common nontrivial element commute with each
other. -/
theorem commute_of_commute_of_commute
    (huv : Commute u v) (huw : Commute u w) (hu : u ≠ 1) : Commute v w := by
  /- As `u` and `v` commute, write `u = r ^ a` and `v = r ^ b`. In the same way,
  `u = s ^ c` and `w = s ^ d`. As `r ^ a = s ^ c`, then `r` and `s` commute, and therefore
  `v = r ^ b` and `w = s ^ d` also commute. -/
  obtain ⟨r, ⟨a, ha⟩, ⟨b, rfl⟩⟩ := commute_iff_exists_mem_zpowers.1 huv
  obtain ⟨s, ⟨c, hc⟩, ⟨d, rfl⟩⟩ := commute_iff_exists_mem_zpowers.1 huw
  simp only at ha hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at hc
    exact hu hc.symm
  have hrs : Commute r s := Commute.of_zpow_eq (by rw [ha, hc]) hc0
  exact hrs.zpow_zpow b d

/-- The centralizer of a nontrivial element of a free group is cyclic. -/
theorem isCyclic_centralizer_singleton (hu : u ≠ 1) : IsCyclic (Subgroup.centralizer {u}) := by
  rw [isCyclic_iff_isMulCommutative, isMulCommutative_iff]
  intro v w
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact commute_of_commute_of_commute (Subgroup.mem_centralizer_singleton_iff.mp v.2).symm
    (Subgroup.mem_centralizer_singleton_iff.mp w.2).symm hu

/-- A nontrivial element of a free group is a nonzero power of a generator of its own centralizer:
there are `r ≠ 1` and `n ≠ 0` with `zpowers r = centralizer {v}` and `u ^ n = v`. -/
theorem exists_zpowers_eq_centralizer_singleton (hu : u ≠ 1) :
    ∃ (r : G) (n : ℤ), r ≠ 1 ∧ n ≠ 0 ∧ Subgroup.centralizer {u} = Subgroup.zpowers r ∧
      u = r ^ n := by
  obtain ⟨r, hr⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq _).mp (isCyclic_centralizer_singleton hu)
  have huC : u ∈ Subgroup.centralizer {u} := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨n, hn⟩ : u ∈ Subgroup.zpowers r := by rwa [hr]
  refine ⟨r, n, ?_, ?_, hr.symm, hn.symm⟩
  · rintro rfl
    exact hu (by simp [← hn])
  · rintro rfl
    exact hu.symm (by simpa using hn)

end IsFreeGroup
