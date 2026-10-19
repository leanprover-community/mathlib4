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
* `FreeGroup.isCyclic_centralizer`: the centralizer of a non-unit element is a cyclic subgroup.
* `FreeGroup.commute_iff_exists_zpow`: two elements of a free group commute iff they are powers of
  the same element.
-/

public section

namespace FreeGroup

variable {α : Type*}

@[to_additive]
theorem mem_zpowers_of_iff [DecidableEq α] {a : α} {x : FreeGroup α} :
    x ∈ Subgroup.zpowers (of a) ↔ ∀ p ∈ x.toWord, p.1 = a := by
  refine ⟨by rintro ⟨_, rfl⟩; simp, fun h ↦ ?_⟩
  by_cases! heq : ∀ p ∈ x.toWord, p.2 = true
  · refine ⟨x.toWord.length, toWord_inj.mp <| List.ext_getElem (by simp) fun i _ hi ↦ ?_⟩
    grind [zpow_natCast, toWord_of_pow]
  refine ⟨-x.toWord.length, toWord_inj.mp <| List.ext_getElem (by simp) fun i _ hi ↦ ?_⟩
  obtain ⟨m, hm, _⟩ := heq
  obtain ⟨j, hj₁, hj₂⟩ := List.mem_iff_getElem.mp hm
  have : x.toWord.Pairwise (·.2 = ·.2) :=
    List.isChain_iff_pairwise.mp <| isReduced_toWord.imp_of_mem_imp <| by grind
  simp [invRev]
  grind [List.pairwise_iff_getElem.mp this (i ⊓ j) (i ⊔ j)]

@[to_additive]
theorem centralizer_of (a : α) : Subgroup.centralizer {of a} = Subgroup.zpowers (of a) := by
  classical
  refine le_antisymm ?_ (by simp [Subgroup.mem_centralizer_singleton_iff])
  refine fun x hx ↦ mem_zpowers_of_iff.mpr fun p hp ↦ ?_
  by_contra! hpne
  have : of a * x = x * of a := by simpa using hx (of a) rfl
  grind [idxOf_toWord_mul_of_eq x hpne hp, idxOf_toWord_of_mul_eq x hpne,
    List.idxOf_eq_zero_iff_eq_nil_or_head_eq]

@[to_additive]
theorem commute_of_iff {a : α} {x : FreeGroup α} :
    Commute (of a) x ↔ x ∈ Subgroup.zpowers (of a) := by
  rw [← centralizer_of, Subgroup.mem_centralizer_singleton_iff, commute_iff_eq, eq_comm]

@[to_additive]
theorem center_eq_top_of_subsingleton [Subsingleton α] : Subgroup.center (FreeGroup α) = ⊤ :=
  Subgroup.center_eq_top

@[to_additive]
theorem center_eq_bot_of_nontrivial [Nontrivial α] : Subgroup.center (FreeGroup α) = ⊥ := by
  obtain ⟨a, b, hab⟩ := ‹_›
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  obtain ⟨n, rfl⟩ := commute_of_iff.mp <| Subgroup.mem_center_iff.mp hx (of a)
  obtain ⟨m, hm⟩ := commute_of_iff.mp <| Subgroup.mem_center_iff.mp hx (of b)
  simp [eq_of_of_zpow_eq_of_zpow hab hm.symm]

@[to_additive]
theorem isCyclic_centralizer {a : FreeGroup α} (ha : a ≠ 1) :
    IsCyclic (Subgroup.centralizer {a}) := by
  obtain ⟨β, ⟨⟨f⟩⟩⟩ := Subgroup.isFreeGroupOfIsFreeGroup (Subgroup.centralizer {a})
  rw [f.isCyclic, isCyclic_iff_subsingleton]
  by_contra!
  have := Subgroup.mem_centralizer_singleton_iff (g := a) |>.mpr rfl
  have : ⟨a, this⟩ ∈ Subgroup.center (Subgroup.centralizer {a}) := by
    simp [Subgroup.mem_center_iff, Subgroup.mem_centralizer_singleton_iff]
  simp [← Subgroup.map_center_eq f.symm, center_eq_bot_of_nontrivial, ha] at this

/-- Free groups are commutative-transitive. -/
@[to_additive /-- Free additive groups are commutative-transitive. -/]
theorem commute_trans {a b c : FreeGroup α} (h₁ : Commute a b) (h₂ : Commute b c) (hb : b ≠ 1) :
    Commute a c := by
  obtain ⟨g, hg⟩ := isCyclic_centralizer hb
  obtain ⟨n, hn⟩ := hg ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr h₁.eq⟩
  obtain ⟨m, hm⟩ := hg ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr h₂.symm.eq⟩
  simp [Subtype.ext_iff] at hn hm
  simp [← hn, ← hm]

@[to_additive]
theorem commute_iff_exists_zpow {a b : FreeGroup α} :
    Commute a b ↔ ∃ c, ∃ n m : ℤ, a = c ^ n ∧ b = c ^ m := by
  refine ⟨fun h ↦ ?_, by simp +contextual⟩
  by_cases hb : b = 1
  · exact ⟨a, 1, 0, by simp [hb]⟩
  obtain ⟨g, hg⟩ := isCyclic_centralizer hb
  obtain ⟨n, hn⟩ := hg ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr h.eq⟩
  obtain ⟨m, hm⟩ := hg ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact ⟨g, n, m, by simp_all [Subtype.ext_iff]⟩

end FreeGroup
