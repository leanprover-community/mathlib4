/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Exchange Property and Accessible Property of Greedoid
Greedoid is a set system, i.e., a family of sets, over a finite ground set, which contains
an empty set and satisfies both exchange and accessible properties.
If a set system `S` satisfies the exchange property, then there is some element `x ∈ s₂ \ s₁`
which `s₁ ∪ {x} ∈ S`, for every set `s₁, s₂ ∈ S` satisfying `s₁.card < s₂.card`.
If a set system `S` satisfies the accessible property, then there is some element `x ∈ s`
which `s \ {x} ∈ G` for every nonempty set `s ∈ S`.
These two properties are defined in this file as `ExchangeProperty` and `AccessibleProperty`.

While it is sufficient to define a greedoid using only the definitions of the properties, it turned
out to be useful to have some theorems equipped with them.
Therefore this file defines exchange property and accessible property, and hands out some basic
theorems which come along with it, prior to defining a greedoid.
-/

namespace Greedoid

open Nat Finset

/-- The exchange property of greedoid.
    Note that the exchange property also hold for matroids. -/
def ExchangeProperty {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → s₁ ∈ Sys →
  {s₂ : Finset α} → s₂ ∈ Sys →
  s₂.card < s₁.card →
  ∃ x ∈ s₁ \ s₂, insert x s₂ ∈ Sys

instance {α : Type _} [DecidableEq α] :
    @DecidablePred (Finset (Finset α)) ExchangeProperty :=
  fun Sys =>
    if h : ∃ s₁ ∈ Sys, ∃ s₂ ∈ Sys, s₂.card < s₁.card ∧ ∀ x ∈ s₁ \ s₂, insert x s₂ ∉ Sys
    then isFalse (fun h' => by
      let ⟨s₁, hs₁, s₂, hs₂, hs₃, hs₄⟩ := h
      have ⟨_, ha₁, ha₂⟩ := h' hs₁ hs₂ hs₃
      exact hs₄ _ ha₁ ha₂)
    else isTrue (by
      simp at h
      intro _ hs₁ _ hs₂ hs
      have ⟨a, ha⟩ := h _ hs₁ _ hs₂ hs
      exists a; simp only [mem_sdiff, ha, not_false_eq_true, and_self])

theorem exchangeProperty_exists_superset_of_card_le {α : Type _} [DecidableEq α]
    {Sys : Finset (Finset α)} (hSys : ExchangeProperty Sys)
    {s₁ : Finset α} (hs₁ : s₁ ∈ Sys)
    {s₂ : Finset α} (hs₂ : s₂ ∈ Sys)
    (hs : s₂.card ≤ s₁.card)
    {n : ℕ} (hn₁ : n ≤ s₁.card) (hn₂ : s₂.card ≤ n) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ s ⊆ s₁ ∪ s₂ ∧ s.card = n := by
  by_cases h : s₂.card = n
  · exists s₂
    simp_all only [Subset.refl, subset_union_right, and_self, hn₁, hs₂]
  · have ⟨x, hx₁, hx₂⟩ := hSys hs₁ hs₂ (lt_iff_le_and_ne.mpr ⟨hs, by
      intro h₁
      apply h
      apply le_antisymm hn₂
      exact h₁ ▸ hn₁⟩)
    have h₁ : (insert x s₂).card = s₂.card + 1 := card_insert_of_not_mem (mem_sdiff.mp hx₁).2
    have ⟨b, hb⟩ := exchangeProperty_exists_superset_of_card_le hSys hs₁ hx₂ (by
      rw [h₁, succ_le, lt_iff_le_and_ne]
      apply And.intro hs
      intro h₂
      apply h
      apply le_antisymm hn₂
      exact h₂ ▸ hn₁) hn₁ (by
      rw [h₁, succ_le]
      exact lt_of_lt_of_le (lt_iff_le_and_ne.mpr ⟨hn₂, h⟩) le_rfl)
    exists b
    exact ⟨hb.1, subset_trans (subset_insert _ _) hb.2.1, by
      intro _ h
      have h := hb.2.2.1 h
      simp only [union_insert, mem_union, mem_insert] at h
      rw [mem_union]
      apply h.elim _ id
      intro h
      simp only [← h, mem_sdiff] at hx₁
      simp only [hx₁, or_false], hb.2.2.2⟩
termination_by s₁.card - s₂.card
decreasing_by
  simp_wf
  rw [h₁, sub_add_eq]
  apply sub_lt _ (by decide)
  rw [tsub_pos_iff_lt, lt_iff_le_and_ne]
  apply And.intro hs
  intro h₂
  apply h
  exact le_antisymm hn₂ (h₂ ▸ hn₁)

-- TODO: Fix name.
theorem exchangeProperty_exists_feasible_superset_add_element_feasible
    {α : Type _} [DecidableEq α]
    {Sys : Finset (Finset α)} (hSys : ExchangeProperty Sys)
    {s₁ : Finset α} (hs₁ : s₁ ∈ Sys)
    {s₂ : Finset α} (hs₂ : s₂ ∈ Sys)
    (hs : s₂ ⊆ s₁)
    {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s ∈ Sys, s₂ ⊆ s ∧ s ⊆ s₁ ∧ a ∉ s ∧ Insert.insert a s ∈ Sys := by
  have h₁ : s₂.card < s₁.card := by
    apply card_lt_card
    simp only [ssubset_def, hs, true_and]
    intro h
    exact ha₂ (h ha₁)
  by_cases h : Insert.insert a s₂ ∈ Sys
  · exists s₂
  · let ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := exchangeProperty_exists_superset_of_card_le hSys hs₁ hs₂
      (card_le_card hs) h₁ (le_succ _)
    have ht₅ : a ∉ t := by
      intro h'
      apply h; clear h
      have h : insert a s₂ = t := by
        apply eq_of_subset_of_card_le
        · intro _ h
          rw [mem_insert] at h
          exact h.elim (fun h => h ▸ h') (fun h => ht₂ h)
        · rw [ht₄, card_insert_of_not_mem ha₂]
      exact h ▸ ht₁
    let ⟨s', hs'₁, hs'₂, hs'₃, hs'₄, hs'₅⟩ :=
      exchangeProperty_exists_feasible_superset_add_element_feasible hSys hs₁ ht₁
        (union_eq_left.mpr hs ▸ ht₃) ha₁ ht₅
    exists s'
    exact ⟨hs'₁, subset_trans ht₂ hs'₂, hs'₃, hs'₄, hs'₅⟩
termination_by s₁.card - s₂.card
decreasing_by
  simp_wf
  rw [ht₄]
  exact sub_succ_lt_self _ _ h₁

/-- The accessible property of greedoid -/
def AccessibleProperty {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) : Prop :=
  {s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

/-- A set system is accessible if there is some element `x` in `s` which `s \ {x}` is also in the
    set system, for each nonempty set `s` of the set system.
    This automatically implies that nonempty accessible set systems contain an empty set. -/
class Accessible {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) : Prop where
  accessible : {s : Finset α} → s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

theorem accessible_accessibleProperty {α : Type _} [DecidableEq α]
    {Sys : Finset (Finset α)} [Accessible Sys] :
    AccessibleProperty Sys := Accessible.accessible

theorem induction_on_accessible {α : Type _} [DecidableEq α]
    {Sys : Finset (Finset α)} [Accessible Sys]
    {s : Finset α} (hs₀ : s ∈ Sys)
    {p : Finset α → Prop}
    (empty : p ∅)
    (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → s ∈ Sys → Insert.insert a s ∈ Sys → p s →
    p (Insert.insert a s)) :
    p s := by
  by_cases h : s = ∅ <;> try exact h ▸ empty
  have ⟨x, hx₁, hx₂⟩ := Accessible.accessible hs₀ h
  have h' := sdiff_insert_insert_of_mem_of_not_mem hx₁ (not_mem_empty x)
  simp only [insert_emptyc_eq, mem_sdiff, mem_singleton, sdiff_empty] at h'
  have : p (Insert.insert x (s \ {x})) := insert (by
      simp only [mem_sdiff, mem_singleton, not_true_eq_false, and_false,
        not_false_eq_true] : x ∉ s \ {x}) hx₂ (by
      simp only [mem_sdiff, mem_singleton, h', hs₀])
    (induction_on_accessible hx₂ empty insert)
  exact h' ▸ this
termination_by s.card
decreasing_by
  simp_wf
  rw [card_sdiff (singleton_subset_iff.mpr hx₁), card_singleton]
  simp only [zero_lt_one, sub_lt (card_pos.mpr ⟨x, hx₁⟩)]

theorem construction_of_accessible {α : Type _} [DecidableEq α]
    {Sys : Finset (Finset α)} [Accessible Sys] (hSys : ∅ ∈ Sys)
    {s : Finset α} (hs₀ : s ∈ Sys) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧ ∀ l', l' <:+ l → l'.toFinset ∈ Sys := by
  apply induction_on_accessible hs₀
  · exists []; simp only [List.nodup_nil, List.toFinset_nil, List.suffix_nil, forall_eq, hSys,
    and_self]
  · simp only [List.mem_tails, forall_exists_index, and_imp]
    intro a s ha _ hs l hl₁ hl₂ hl₃
    exists a :: l
    simp only [List.nodup_cons, hl₁, and_true, List.toFinset_cons, hl₂, true_and]
    have : a ∉ l := by simp only [← hl₂, List.mem_toFinset] at ha; exact ha
    simp only [this, not_false_eq_true, true_and]
    intro l' hl'
    rw [List.suffix_cons_iff] at hl'
    apply hl'.elim <;> intro hl'
    · simp only [hl', List.toFinset_cons, hl₂, hs]
    · exact hl₃ _ hl'

end Greedoid
