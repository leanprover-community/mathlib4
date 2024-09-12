/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.Pointwise.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinalities of pointwise operations on sets.
-/

open Pointwise

variable {α β : Type*}

namespace Finset

section One

variable [One α]

@[to_additive (attr := simp)]
theorem card_one : (1 : Finset α).card = 1 :=
  card_singleton _

end One

section Inv

variable [DecidableEq α] [Inv α] {s : Finset α}

@[to_additive]
theorem card_inv_le : s⁻¹.card ≤ s.card :=
  card_image_le

end Inv

section InvolutiveInv
variable [DecidableEq α] [InvolutiveInv α] {s : Finset α}

@[to_additive (attr := simp)]
theorem card_inv (s : Finset α) : s⁻¹.card = s.card := card_image_of_injective _ inv_injective

end InvolutiveInv

section Mul

variable [DecidableEq α] [Mul α] [Mul β] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

@[to_additive]
theorem card_mul_le : (s * t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _

@[to_additive]
theorem card_mul_iff :
    (s * t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff

end Mul

section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

@[to_additive]
theorem div_card_le : (s / t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _

end Div

section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

@[to_additive]
theorem smul_card_le : (s • t).card ≤ s.card • t.card :=
  card_image₂_le _ _ _

end SMul

section VSub

-- Porting note: Reordered [VSub α β] and [DecidableEq α] to make vsub less dangerous. Bad?
variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

theorem vsub_card_le : (s -ᵥ t : Finset α).card ≤ s.card * t.card :=
  card_image₂_le _ _ _

end VSub

section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t u : Finset β} {a : α} {b : β}

@[to_additive]
theorem smul_finset_card_le : (a • s).card ≤ s.card :=
  card_image_le

end SMul

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] (s t : Finset α) (a : α)

@[to_additive (attr := simp)]
theorem card_singleton_mul : ({a} * t).card = t.card :=
  card_image₂_singleton_left _ <| mul_right_injective _

@[to_additive]
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : t.card ≤ (s * t).card :=
  card_le_card_image₂_left _ hs mul_right_injective

end IsLeftCancelMul

section

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] (s t : Finset α) (a : α)

@[to_additive (attr := simp)]
theorem card_mul_singleton : (s * {a}).card = s.card :=
  card_image₂_singleton_right _ <| mul_left_injective _

@[to_additive]
theorem card_le_card_mul_right {t : Finset α} (ht : t.Nonempty) : s.card ≤ (s * t).card :=
  card_le_card_image₂_right _ ht mul_left_injective

end

section Group
variable [Group α] [DecidableEq α] {s t : Finset α}

@[to_additive] lemma card_le_card_div_left (hs : s.Nonempty) : t.card ≤ (s / t).card :=
  card_le_card_image₂_left _ hs fun _ ↦ div_right_injective

@[to_additive] lemma card_le_card_div_right (ht : t.Nonempty) : s.card ≤ (s / t).card :=
  card_le_card_image₂_right _ ht fun _ ↦ div_left_injective

end Group


section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[to_additive (attr := simp)]
theorem card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card :=
  card_image_of_injective _ <| MulAction.injective _

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s • t`. -/
@[to_additive "If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s +ᵥ t`."]
theorem card_dvd_card_smul_right {s : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun _ _ => MulAction.injective _

variable [DecidableEq α]

/-- If the right cosets of `s` by elements of `t` are disjoint (but not necessarily distinct!), then
the size of `s` divides the size of `s * t`. -/
@[to_additive "If the right cosets of `s` by elements of `t` are disjoint (but not necessarily
distinct!), then the size of `s` divides the size of `s + t`."]
theorem card_dvd_card_mul_left {s t : Finset α} :
    ((fun b => s.image fun a => a * b) '' (t : Set α)).PairwiseDisjoint id →
      s.card ∣ (s * t).card :=
  card_dvd_card_image₂_left fun _ _ => mul_left_injective _

/-- If the left cosets of `t` by elements of `s` are disjoint (but not necessarily distinct!), then
the size of `t` divides the size of `s * t`. -/
@[to_additive "If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s + t`."]
theorem card_dvd_card_mul_right {s t : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s * t).card :=
  card_dvd_card_image₂_right fun _ _ => mul_right_injective _

end Group

end Finset

namespace Set

section MulAction
variable [Group α] [MulAction α β]

@[to_additive (attr := simp)]
lemma card_smul_set (a : α) (s : Set β) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective a) _

end MulAction

section IsCancelMul
variable [Mul α] [IsCancelMul α] {s t : Set α}

@[to_additive]
lemma card_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  classical
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  obtain ⟨hs, ht⟩ | rfl | rfl := Set.finite_mul.1 h
  · lift s to Finset α using hs
    lift t to Finset α using ht
    rw [← Finset.coe_mul]
    simpa [-Finset.coe_mul] using Finset.card_mul_le
  all_goals simp

end IsCancelMul

section InvolutiveInv
variable [InvolutiveInv α] {s t : Set α}

@[to_additive (attr := simp)]
lemma card_inv (s : Set α) : Nat.card ↥(s⁻¹) = Nat.card s := by
  rw [← image_inv, Nat.card_image_of_injective inv_injective]

end InvolutiveInv

section Group
variable [Group α] {s t : Set α}

@[to_additive]
lemma card_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← card_inv t]; exact card_mul_le

end Group
end Set
