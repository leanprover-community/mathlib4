/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The `Filter.atMax` and `Filter.atMin` filters

We define the filters `Filter.atMax` and `Filter.atMin`.
-/

variable {α : Type*}

open Set

namespace Filter

/--
`atMax` is the filter representing the limit `→ ∞` on an ordered set,
and contains all maximal elements.
-/
def atMax [Preorder α] : Filter α where
  sets := {s | ∀ x, ∃ y ≥ x, Ici y ⊆ s}
  univ_sets := fun x => ⟨x, le_rfl, subset_univ _⟩
  sets_of_superset := by
    intro s t hs hst x
    obtain ⟨y, hxy, hy⟩ := hs x
    exact ⟨y, hxy, hy.trans hst⟩
  inter_sets := by
    intro s t hs ht x
    obtain ⟨y, hxy, hy⟩ := hs x
    obtain ⟨z, hyz, hz⟩ := ht y
    exact ⟨z, hxy.trans hyz, subset_inter ((Ici_subset_Ici.mpr hyz).trans hy) hz⟩

/--
`atMin` is the filter representing the limit `→ -∞` on an ordered set,
and contains all minimal elements.
-/
def atMin [Preorder α] : Filter α where
  sets := {s | ∀ x, ∃ y ≤ x, Iic y ⊆ s}
  univ_sets := fun x => ⟨x, le_rfl, subset_univ _⟩
  sets_of_superset := by
    intro s t hs hst x
    obtain ⟨y, hyx, hy⟩ := hs x
    exact ⟨y, hyx, hy.trans hst⟩
  inter_sets := by
    intro s t hs ht x
    obtain ⟨y, hyx, hy⟩ := hs x
    obtain ⟨z, hzy, hz⟩ := ht y
    exact ⟨z, hzy.trans hyx, subset_inter ((Iic_subset_Iic.mpr hzy).trans hy) hz⟩

theorem mem_atMax [Preorder α] (s : Set α) : s ∈ atMax ↔ ∀ x, ∃ y ≥ x, Ici y ⊆ s := Iff.rfl
theorem mem_atMin [Preorder α] (s : Set α) : s ∈ atMin ↔ ∀ x, ∃ y ≤ x, Iic y ⊆ s := Iff.rfl

instance [Preorder α] [Nonempty α] : NeBot (atMax : Filter α) where
  ne' := by
    intro h
    rw [← empty_mem_iff_bot, mem_atMax] at h
    obtain ⟨x⟩ := ‹Nonempty α›
    obtain ⟨y, _, hy⟩ := h x
    exact hy le_rfl

instance [Preorder α] [Nonempty α] : NeBot (atMin : Filter α) where
  ne' := by
    intro h
    rw [← empty_mem_iff_bot, mem_atMin] at h
    obtain ⟨x⟩ := ‹Nonempty α›
    obtain ⟨y, _, hy⟩ := h x
    exact hy le_rfl

theorem atTop_le_atMax [Preorder α] : (atTop : Filter α) ≤ atMax := by
  intro s hs
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty α
  · rw [atTop.filter_eq_bot_of_isEmpty]
    exact mem_bot
  · rw [mem_atMax] at hs
    obtain ⟨y, _, hy⟩ := hs x
    filter_upwards [Ici_mem_atTop y] using hy

theorem atBot_le_atMin [Preorder α] : (atBot : Filter α) ≤ atMin := by
  intro s hs
  obtain h | ⟨⟨x⟩⟩ := isEmpty_or_nonempty α
  · rw [atBot.filter_eq_bot_of_isEmpty]
    exact mem_bot
  · rw [mem_atMin] at hs
    obtain ⟨y, _, hy⟩ := hs x
    filter_upwards [Iic_mem_atBot y] using hy

theorem atMax_eq_atTop [Preorder α] [IsDirected α (· ≤ ·)] : (atMax : Filter α) = atTop := by
  apply atTop_le_atMax.antisymm'
  intro s hs x
  have : Nonempty α := ⟨x⟩
  rw [mem_atTop_sets] at hs
  obtain ⟨y, hy⟩ := hs
  obtain ⟨z, hxz, hyz⟩ := exists_ge_ge x y
  exact ⟨z, hxz, fun u hzu => hy u (hyz.trans hzu)⟩

theorem atMin_eq_atBot [Preorder α] [IsDirected α (· ≥ ·)] : (atMin : Filter α) = atBot := by
  apply atBot_le_atMin.antisymm'
  intro s hs x
  have : Nonempty α := ⟨x⟩
  rw [mem_atBot_sets] at hs
  obtain ⟨y, hy⟩ := hs
  obtain ⟨z, hzx, hzy⟩ := exists_le_le x y
  exact ⟨z, hzx, fun u huz => hy u (huz.trans hzy)⟩

theorem pure_le_atMax [Preorder α] (x : α) : pure x ≤ atMax ↔ IsMax x := by
  constructor
  · intro h
    by_contra hx
    rw [not_isMax_iff] at hx
    obtain ⟨y, hxy⟩ := hx
    suffices hy : (Iio y)ᶜ ∈ atMax from h hy hxy
    intro z
    by_cases hzy : z ≤ y
    · exact ⟨y, hzy, fun u hyu huy => huy.not_le hyu⟩
    · exact ⟨z, le_rfl, fun u hzu huy => hzy (hzu.trans huy.le)⟩
  · intro hx s hs
    rw [mem_atMax] at hs
    obtain ⟨y, hxy, hy⟩ := hs x
    exact hy (hx hxy)

theorem pure_le_atMin [Preorder α] (x : α) : pure x ≤ atMin ↔ IsMin x := by
  constructor
  · intro h
    by_contra hx
    rw [not_isMin_iff] at hx
    obtain ⟨y, hxy⟩ := hx
    suffices hy : (Ioi y)ᶜ ∈ atMin from h hy hxy
    intro z
    by_cases hyz : y ≤ z
    · exact ⟨y, hyz, fun u huy hyu => hyu.not_le huy⟩
    · exact ⟨z, le_rfl, fun u huz hyu => hyz (hyu.le.trans huz)⟩
  · intro hx s hs
    rw [mem_atMin] at hs
    obtain ⟨y, hyx, hy⟩ := hs x
    exact hy (hx hyx)

end Filter
