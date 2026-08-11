/-
Copyright (c) 2026 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
module

public import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Center and centralizer of free groups

This file develops the basic theory of center and the centralizer of a single element of a
free group.

## Main statements

* `center_eq_top_of_subsingleton`/`center_eq_bot_of_nontrivial`: the center of a free group is
  `⊤` or `⊥`, depending on the number of generators.
* `isCyclic_centralizer`: the centralizer of a non-unit element is always a cyclic subgroup.
-/

@[expose] public section

namespace FreeGroup

variable {α : Type*}

@[to_additive]
theorem centralizer_of_eq_closure (a : α) :
    Subgroup.centralizer { of a } = Subgroup.closure { of a } := by
  classical
  refine le_antisymm ?_ (by simp [Subgroup.mem_centralizer_singleton_iff])
  by_contra! hh
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.not_le_iff_exists.mp hh
  simp only [mem_closure_iff, not_forall] at hx₂
  obtain ⟨n, hn, hx⟩ := hx₂
  have : of a * x = x * of a := by simpa using hx₁ (of a) rfl
  grind [idxOf_toWord_mul_of_eq x hx, idxOf_toWord_of_mul_eq x hx,
    List.idxOf_eq_zero_iff_eq_nil_or_head_eq]

@[to_additive]
theorem center_eq_top_of_subsingleton [Subsingleton α] : Subgroup.center (FreeGroup α) = ⊤ :=
  Subgroup.center_eq_top

@[to_additive]
theorem center_eq_bot_of_nontrivial [Nontrivial α] : Subgroup.center (FreeGroup α) = ⊥ := by
  obtain ⟨a, b, hab⟩ := ‹_›
  grw [eq_bot_iff, Subgroup.center_le_centralizer {of a, of b}]
  have : Subgroup.centralizer { of a } ⊓ Subgroup.centralizer { of b } = ⊥ := by
    ext x
    refine ⟨fun ⟨ha, hb⟩ ↦ ?_, by simp +contextual⟩
    rw [Subgroup.coe_toSubmonoid, SetLike.mem_coe, centralizer_of_eq_closure,
      Subgroup.mem_closure_singleton] at ha hb
    obtain ⟨n, hn⟩ := ha
    obtain ⟨m, hm⟩ := hb
    simpa [eq_of_of_zpow_eq_of_zpow hab (hm ▸ hn)] using hm.symm
  grind [le_inf_iff, Subgroup.centralizer_le]

@[to_additive]
theorem isCyclic_centralizer (a : FreeGroup α) (ha : a ≠ 1) :
    IsCyclic (Subgroup.centralizer { a }) := by
  obtain ⟨β, ⟨⟨f⟩⟩⟩ := subgroupIsFreeGroupOfIsFreeGroup (Subgroup.centralizer { a })
  rw [f.isCyclic, ← FreeGroup.subsingleton_iff_isCyclic]
  have : Subgroup.center (Subgroup.centralizer { a }) ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
    refine ⟨⟨⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩, ?_⟩
    · simp [Subgroup.mem_center_iff, Subgroup.mem_centralizer_singleton_iff]
    · simp [ha]
  contrapose! this
  simp [← Subgroup.map_center_of_mulEquiv f.symm, center_eq_bot_of_nontrivial]

/-- Free groups are commutative-transitive. -/
@[to_additive]
theorem commute_of_commute {a b c : FreeGroup α} (h₁ : Commute a b)
    (h₂ : Commute b c) (hb : b ≠ 1) : Commute a c := by
  obtain ⟨x, hx⟩ := isCyclic_centralizer b hb
  obtain ⟨y, hy⟩ := hx ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr h₁.eq⟩
  obtain ⟨z, hz⟩ := hx ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr h₂.symm.eq⟩
  simp [Subtype.ext_iff] at hy hz
  simp [← hy, ← hz]

end FreeGroup
