/-
Copyright (c) 2024 Jihoon Hyun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jihoon Hyun
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Greedoid.Accessible
import Mathlib.Data.Set.Finite
import Init.Data.Nat.Basic

/-!
This file contains the definition of `ExchangeProperty`,
along with some main properties of set systems with the exchange property.
Not to be confused with 'Exchange System'. [Brylawski & Dieter, 1986]

# Exchange property
A set system `S` satisfies the exchange property if there is some `x ∈ s \ t` for `s, t ∈ S`
which `t.card < s.card`, that `t ∪ {x} ∈ S`.
-/

namespace Greedoid

open Nat Finset

variable {α : Type*}

-- TODO: Is typeclass `Exchange` required?
/-- The exchange property of greedoid.
    Note that the exchange property also hold for (finite) matroids.

    A set system satisfies the exchange property if there is some element `x` in some feasible
    `s₁`, which is not in `s₂` with smaller cardinaliy, and `s₂ ∪ {x}` is also feasible.
    This implies that all maximal feasible sets are actually maximum. -/
def ExchangeProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s₁ : Finset α⦄ → Sys s₁ →
  ⦃s₂ : Finset α⦄ → Sys s₂ →
  s₂.card < s₁.card →
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, Sys (cons x s₂ h)

namespace ExchangeProperty

open Nat Finset

variable {Sys : Finset α → Prop}
variable {s₁ : Finset α} {s₂ : Finset α}

-- TODO: Find a better name.
theorem exists_superset_of_card_le
    (hS : ExchangeProperty Sys) (hs₁ : Sys s₁) (hs₂ : Sys s₂)
    {n : ℕ} (hn₁ : n ≤ s₁.card) (hn₂ : s₂.card ≤ n) :
    ∃ s, Sys s ∧ s₂ ⊆ s ∧ (∀ e ∈ s, e ∈ s₁ ∨ e ∈ s₂) ∧ s.card = n := by
    induction n, hn₂ using le_induction with
    | base => use s₂; simp [hs₂]; intro _ h; exact .inr h
    | succ _ h ih =>
      rcases ih (by omega) with ⟨s, hs, h₁, h₂, rfl⟩
      rcases hS hs₁ hs hn₁ with ⟨a, ha₁, ha₂, ha₃⟩
      use cons a s ha₂; simp_all
      intro _ h; simp [h₁ h]

-- TODO: Find a better name.
theorem exists_feasible_superset_add_element_feasible
    (hS : ExchangeProperty Sys) (hs₁ : Sys s₁) (hs₂ : Sys s₂) (hs : s₂ ⊆ s₁)
    {a : α} (ha₁ : a ∈ s₁) (ha₂ : a ∉ s₂) :
    ∃ s, Sys s ∧ s₂ ⊆ s ∧ s ⊆ s₁ ∧ ∃ h : a ∉ s, Sys (cons a s h) := by
  induction' hn : s₁.card - s₂.card generalizing s₂
  case zero =>
    exact False.elim ((eq_of_subset_of_card_le hs (Nat.le_of_sub_eq_zero hn) ▸ ha₂) ha₁)
  case succ _ ih =>
    rcases exists_superset_of_card_le hS hs₁ hs₂ (by omega) (le_succ _)
      with ⟨s, hs₃, hs₄, hs₅, hs₆⟩
    by_cases h : a ∈ s
    · use s₂; simp [hs₂, hs, ha₂]
      exact (eq_of_subset_of_card_le
        ((@cons_subset _ _ _ _ ha₂).mpr ⟨h, hs₄⟩)  (hs₆ ▸ card_cons ha₂ ▸ le_rfl)) ▸ hs₃
    · rcases ih hs₃ (fun e h ↦ (hs₅ _ h).elim id (fun f ↦ hs f)) h (by omega)
        with ⟨t, ht⟩
      use t; simp [ht, subset_trans hs₄]

end ExchangeProperty

section ExchangePropertyEquivalence

open Accessible Nat Finset

variable {Sys : Finset α → Prop}

/-- A weak version of `ExchangeProperty`.
    This is equivalent to `ExchangeProperty` under `Accessible` assumption. -/
def WeakExchangeProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s₁ : Finset α⦄ → (hs₁ : Sys s₁) →
  ⦃s₂ : Finset α⦄ → (hs₂ : Sys s₂) →
  (hs : s₂.card + 1 = s₁.card) →
    ∃ x ∈ s₁, ∃ h : x ∉ s₂, Sys (s₂.cons x h)

theorem weakExchangeProperty_of_exchangeProperty
    (h : ExchangeProperty Sys) :
    WeakExchangeProperty Sys := by
  intro _ hs₁ _ hs₂ hs; apply h hs₁ hs₂; omega

theorem exchangeProperty_of_weakExchangeProperty
    [Accessible Sys] (h : WeakExchangeProperty Sys) :
    ExchangeProperty Sys := by
  intro s₁ hs₁ s₂ hs₂ hs
  induction hs₁ using induction_on_accessible (nonempty_contains_emptyset ⟨_, hs₁⟩) with
  | empty => simp at hs
  | insert ht _ht h₁ h₂ ih =>
    rename_i t₁ t₂
    by_cases h₃ : s₂.card < t₂.card
    · rcases ih h₃ with ⟨u, hu₁, hu₂, hu₃⟩
      use u; exact ⟨h₁ hu₁, hu₂, hu₃⟩
    · rw [(by omega : t₂.card = s₂.card)] at h₂
      exact h ht hs₂ h₂

theorem exchangeProperty_iff_weakExchangeProperty
    [Accessible Sys] :
    ExchangeProperty Sys ↔ WeakExchangeProperty Sys :=
  ⟨weakExchangeProperty_of_exchangeProperty, exchangeProperty_of_weakExchangeProperty⟩

/-- A weaker version of `ExchangeProperty`.
    This is equivalent to `ExchangeProperty` under `Accessible` assumption. -/
def WeakerExchangeProperty (Sys : Finset α → Prop) : Prop :=
  ⦃s : Finset α⦄ →
  ⦃x : α⦄ → (hx₁ : x ∉ s) → (hx₂ : Sys (s.cons x hx₁)) →
  ⦃y : α⦄ → (hy₁ : y ∉ s) → (hy₂ : Sys (s.cons y hy₁)) → (hxy₁ : x ≠ y) →
  ⦃z : α⦄ → (hz : z ∉ s) → (hxz₁ : x ≠ z) →
  (hxz₂ : Sys ((s.cons x hx₁).cons z (by rw [mem_cons, not_or]; exact ⟨Ne.symm hxz₁, hz⟩))) →
  (hxy₂ : ¬ Sys ((s.cons x hx₁).cons y (by rw [mem_cons, not_or]; exact ⟨Ne.symm hxy₁, hy₁⟩))) →
    Sys ((s.cons y hy₁).cons z (by rw [mem_cons, not_or]; exact ⟨(fun h ↦ hxy₂ (h ▸ hxz₂)), hz⟩))

theorem weakerExchangeProperty_of_weakExchangeProperty
    (h : WeakExchangeProperty Sys) :
    WeakerExchangeProperty Sys := by
  intro s x hx₁ hx₂ y hy₁ hy₂ hxy₁ z hz hxz₁ hxz₂ hxy₂
  rcases h hxz₂ hy₂ (by simp only [card_cons]) with ⟨u, hu₁, hu₂, hu₃⟩
  simp only [mem_cons, not_or] at hu₁ hu₂; simp only [hu₂, or_false] at hu₁
  apply hu₁.elim (fun h ↦ h ▸ hu₃); rintro rfl
  exact False.elim (hxy₂ (Finset.cons_swap _ _ ▸ hu₃))

theorem weakExchangeProperty_of_weakerExchangeProperty
    [Accessible Sys] (h : WeakerExchangeProperty Sys) :
    WeakExchangeProperty Sys := by
  intro s₁ hs₁ s₂ hs₂ hs
  have h₁ : ∃ c : Finset α, c ⊆ s₁ ∧ c ⊆ s₂ ∧ Sys c ∧ ∀ s, s ⊆ s₁ → s ⊆ s₂ → Sys s →
      s.card ≤ c.card := by
    sorry
  sorry

end ExchangePropertyEquivalence

end Greedoid

