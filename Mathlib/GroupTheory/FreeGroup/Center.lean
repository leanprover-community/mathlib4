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
# Center and centralizers of free groups

This file develops the theory of commuting elements in a free group.

## Main statements

* `FreeGroup.center_eq_top_of_subsingleton` and `FreeGroup.center_eq_bot_of_nontrivial`: the center
  of a free group is `⊤` or `⊥`, depending on the number of generators.
* `IsFreeGroup.isCyclic_centralizer`: the centralizer of a non-unit element is a cyclic subgroup.
* `IsFreeGroup.commute_iff_exists_zpow`: two elements of a free group commute iff they are powers of
  the same element.
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
theorem center_eq_bot_or_top : Subgroup.center G = ⊥ ∨ Subgroup.center G = ⊤ := by
  have e := IsFreeGroup.mulEquiv G
  rw [← map_bot (e : FreeGroup (Generators G) →* G), ← map_equiv_top e, ← map_center_eq e,
    (map_injective e.injective).eq_iff, (map_injective e.injective).eq_iff]
  refine (subsingleton_or_nontrivial (Generators G)).symm.imp ?_ ?_
  · exact fun h ↦ FreeGroup.center_eq_bot_of_nontrivial
  · exact fun h ↦ FreeGroup.center_eq_top_of_subsingleton

@[to_additive]
theorem isCyclic_centralizer {g : G} (ha : g ≠ 1) :
    IsCyclic (Subgroup.centralizer {g}) := by
  rw [IsFreeGroup.isCyclic_iff_isMulCommutative, ← Subgroup.center_eq_top_iff]
  apply IsFreeGroup.center_eq_bot_or_top.resolve_left
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
