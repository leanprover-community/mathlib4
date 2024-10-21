/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Init.Data.Nat.Basic

/-!
This file contains the definition of `AccessibleProperty` and `Accessible` typeclass,
along with some main properties of accessible set systems.

# Accessible
A set system `S` is accessible if there is some `x ∈ s` which `s \ {x} ∈ S` for each `s ∈ S`.
This is equivalent to saying that `S` is accessible if there is some `t ⊆ s` which `t ∈ S` and
`t.card + 1 = s.card`, for each `s ∈ S`.
This file uses the latter definition to remove a `DecidableEq` condition which is required
when using the former definition.
-/

namespace Greedoid

open Nat Finset List

variable {α : Type*}

/-- The accessible property of greedoid. -/
def AccessibleProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s : Finset α⦄ → Sys s → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ Sys t

/-- A set system is accessible if there is some element `x` in `s` which `s \ {x}` is also in the
    set system, for each nonempty set `s` of the set system.
    This automatically implies that nonempty accessible set systems contain an empty set. -/
class Accessible (Sys : Finset α → Prop) : Prop where
  accessible :
    ⦃s : Finset α⦄ → Sys s → s.Nonempty → ∃ t, t ⊆ s ∧ t.card + 1 = s.card ∧ Sys t

namespace Accessible

variable {Sys : Finset α → Prop} [Accessible Sys]

theorem nonempty_contains_emptyset
    {s : Finset α} (hs : Sys s) :
    Sys ∅ := by
  induction' h : s.card generalizing s
  case zero => exact card_eq_zero.mp h ▸ hs
  case succ _ ih =>
    rcases accessible hs (by rw [← card_ne_zero]; omega) with ⟨_, _, _, h⟩
    exact ih h (by omega)

@[simp]
theorem nonempty_contains_emptyset_iff :
    (∃ s, Sys s) ↔ Sys ∅ :=
  ⟨fun ⟨_, hs⟩ => nonempty_contains_emptyset hs, fun h => ⟨∅, h⟩⟩

-- TODO: Find better name.
-- TODO: Find a better way to inform `hS`.
--       `hS` can be obtained by `hs`.
theorem induction_on_accessible
    (hS : Sys ∅)
    {p : ⦃s : Finset α⦄ → Sys s → Prop}
    (empty : p hS)
    (insert :
      ∀ ⦃s₁ : Finset α⦄, (hs₁ : Sys s₁) →
      ∀ ⦃s₂ : Finset α⦄, (hs₂ : Sys s₂) →
      s₂ ⊆ s₁ → s₂.card + 1 = s₁.card → p hs₂ → p hs₁)
    {s : Finset α} (hs : Sys s):
    p hs := by
  induction' hn : s.card generalizing s
  case zero => exact card_eq_zero.mp hn ▸ empty
  case succ n ih =>
    rcases accessible hs (one_le_card.mp (by omega)) with ⟨t, ht₁, ht₂, ht₃⟩
    exact insert hs ht₃ ht₁ ht₂ (ih ht₃ (by omega))

-- TODO: Find better name.
theorem construction_on_accessible
    [DecidableEq α] {s : Finset α} (hs : Sys s) :
    ∃ l : List α, l.Nodup ∧ Multiset.ofList l = s.val ∧ ∀ l', l' <:+ l →
      ∃ s', Multiset.ofList l' = s'.val ∧ Sys s' := by
  have hS := nonempty_contains_emptyset hs
  induction hs using induction_on_accessible hS with
  | empty => use []; simp; use ∅; simp [hS]
  | insert hs hs₂ h₁ h₂ h₃ =>
    rename_i s₁ s₂; clear hs₂; rcases h₃ with ⟨l₀, hl₀₁, hl₀₂, hl₀₃⟩
    have h₃ : ∃! a, a ∈ s₁ ∧ a ∉ l₀ := by
      have h₃ : (s₁ \ s₂).card = 1 := by rw [card_sdiff h₁]; omega
      rcases card_eq_one.mp h₃ with ⟨a, ha⟩; rw [eq_singleton_iff_unique_mem] at ha
      rcases ha with ⟨h₄, h₅⟩; simp at h₄ h₅
      rw [← @mem_val _ _ s₂, ← hl₀₂, Multiset.mem_coe] at h₄
      use a; simp [h₄, h₅]; intro _ h₁ h₂; apply h₅ _ h₁
      intro h; apply h₂; rw [← Multiset.mem_coe, hl₀₂, mem_val]; exact h
    let x : α := s₁.choose (· ∉ l₀) h₃; have hx : x ∉ l₀ := choose_property _ _ h₃; use x :: l₀
    have h₄ : ↑(x :: l₀) ≤ s₁.val := by
      rw [Multiset.le_iff_count]; intro a
      by_cases ha : a = x
      · simp_all [Multiset.nodup_iff_count_eq_one.mp s₁.nodup x (choose_mem _ _ h₃)]
      · simp [ha]; rw [← Multiset.coe_count, hl₀₂]
        exact Multiset.count_le_of_le _ (val_le_iff.mpr h₁)
    have h₅ : Multiset.card s₁.val ≤ Multiset.card (Multiset.ofList (x :: l₀)) := by
      simp [← h₂, ← card_val s₂, ← hl₀₂]
    have h₆ := Multiset.eq_of_le_of_card_le h₄ h₅
    apply And.intro (by simp [hl₀₁, hx]) (And.intro h₆ _)
    intro l' hl'; rw [suffix_cons_iff] at hl'; apply hl'.elim _ (fun h => hl₀₃ _ h)
    intro hl'; use s₁; simp [hs, hl', h₆]

end Accessible

end Greedoid

